// Connect a real macOS keyboard to the CapslockMode machine.
//
//     swiftc -O drivers/quartz_bridge.swift -o capslockmode-quartz
//     ./capslockmode-quartz --binary ./.lake/build/bin/capslockmode
//
// The bridge does the three things that need a platform and a permission, and
// nothing else:
//
//   1. take a Quartz event tap, so keystrokes can be swallowed before they
//      reach applications;
//   2. hand every event to `capslockmode run --wire quartz` over a pipe;
//   3. post whatever comes back, marked as ours so the tap ignores it.
//
// All the policy -- what `dd` means, which keystrokes that is on a Mac -- lives
// in the Lean program. Keycodes travel on the wire as numbers, so this file
// needs no key table at all.
//
// NOTE: this driver has not been run on real hardware. It is written against
// the documented CoreGraphics API and the Lean side is tested, but the first
// person to run it should expect to fix something.

import Foundation
import CoreGraphics
import ApplicationServices
import AppKit

// MARK: - Options

struct Options {
    var binary = "./capslockmode"
    var toggle = "f18"
    var remap = true
    var dryRun = false
    var check = false
    var monitor = false
}

func parseArgs() -> Options {
    var o = Options()
    var it = CommandLine.arguments.dropFirst().makeIterator()
    while let arg = it.next() {
        switch arg {
        case "--binary": o.binary = it.next() ?? o.binary
        case "--toggle": o.toggle = it.next() ?? o.toggle
        case "--no-remap": o.remap = false
        case "--dry-run": o.dryRun = true
        case "--check": o.check = true
        case "--monitor", "--gui": o.monitor = true
        case "--help", "-h":
            print("""
            capslockmode-quartz - macOS keyboard driver for CapslockMode

              --binary <path>   the capslockmode executable (or set CAPSLOCKMODE_BIN)
              --toggle <key>    key that switches modes (default: f18, see --no-remap)
              --no-remap        do not remap Caps Lock to F18 with hidutil
              --dry-run         print what would be injected instead of injecting it
              --check           report Accessibility permission status and exit
              --monitor         open a window showing intercepted events (starts disarmed)
            """)
            exit(0)
        default:
            FileHandle.standardError.write("unknown option: \(arg)\n".data(using: .utf8)!)
            exit(2)
        }
    }
    if let env = ProcessInfo.processInfo.environment["CAPSLOCKMODE_BIN"] {
        o.binary = env
    } else if o.binary == "./capslockmode" {
        // default to a sibling of this executable, which is how Homebrew installs it
        let here = URL(fileURLWithPath: CommandLine.arguments[0]).deletingLastPathComponent()
        o.binary = here.appendingPathComponent("capslockmode").path
    }

    // Launched from an .app bundle -- double-clicked, or via `open` -- there is
    // no argv to speak of, and the headless branch would sit on a run loop with
    // no window and nothing to look at.  A bundle is only ever built for the
    // monitor, so that is the sane default when nothing was asked for.
    if CommandLine.arguments.count == 1, Bundle.main.bundleIdentifier != nil {
        o.monitor = true
    }
    return o
}

let opts = parseArgs()

// MARK: - The monitor's buffer
//
// Everything the window shows arrives here first.  The point of the indirection
// is the tap callback: CoreGraphics switches off a tap that misses its deadline,
// and the callback runs on the main thread -- the same thread that would draw
// the window.  So nothing on the hot path is allowed to touch AppKit, or even to
// dispatch to it; producers append under a lock and a timer drains them.

final class LogBuffer {
    private let lock = NSLock()
    private var pending: [String] = []
    private var state: String?
    private var dropped = 0
    private let cap = 8192

    func append(_ s: String) {
        lock.lock()
        defer { lock.unlock() }
        // Drop the oldest rather than grow without bound: a wedged UI must not
        // turn into a memory leak driven by the keyboard.
        if pending.count >= cap {
            pending.removeFirst()
            dropped += 1
        }
        pending.append(s)
    }

    /// A `mon` line from the machine, with its prefix already removed.
    func accept(_ s: String) {
        if s.hasPrefix("state ") {
            lock.lock()
            state = String(s.dropFirst("state ".count))
            lock.unlock()
        } else if s.hasPrefix("row ") {
            append(String(s.dropFirst("row ".count)))
        } else if s.hasPrefix("header ") {
            append(String(s.dropFirst("header ".count)))
        } else if s.hasPrefix("device ") {
            append("  -- " + String(s.dropFirst("device ".count)))
        } else if s.hasPrefix("drop ") {
            // A wire line the machine could not turn into anything. Marked so it
            // stands out: this is the shape a missing keycode-table entry takes.
            append("  !! dropped, no key of that code: " + String(s.dropFirst("drop ".count)))
        } else {
            append(s)
        }
    }

    func drain() -> (lines: [String], state: String?, dropped: Int) {
        lock.lock()
        defer { lock.unlock() }
        let l = pending, st = state, d = dropped
        pending = []
        state = nil
        dropped = 0
        return (l, st, d)
    }
}

let logBuffer = LogBuffer()
/// The toggle key and the remap are settings, not constants: with another
/// remapper (kanata, Karabiner) already holding Caps Lock, the defaults are
/// unusable and have to be changed without restarting.
var currentToggle = opts.toggle
var remapEnabled = opts.remap
/// How many events the tap has handed to the machine.  Counted rather than
/// logged, so the hot path allocates nothing: it is the one number that proves
/// the tap is alive even when the machine is not answering.
var eventsSeen = 0
let machineErr = Pipe()

func log(_ s: String) {
    FileHandle.standardError.write("\(s)\n".data(using: .utf8)!)
    logBuffer.append(s)
}

// MARK: - Accessibility

// A tap that *modifies* events needs Accessibility. macOS identifies this
// binary by its code signature, so an ad-hoc signed build loses the grant every
// time it is rebuilt: the entry has to be removed and re-added.
func isTrusted(prompting: Bool) -> Bool {
    let key = kAXTrustedCheckOptionPrompt.takeUnretainedValue() as String
    return AXIsProcessTrustedWithOptions([key: prompting] as CFDictionary)
}

func waitForTrust() {
    if isTrusted(prompting: true) { return }
    log("""
        # not trusted for Accessibility yet.
        # Add this binary under System Settings -> Privacy & Security -> Accessibility:
        #   \(URL(fileURLWithPath: CommandLine.arguments[0]).standardizedFileURL.path)
        # Waiting for the permission; no restart needed once you tick the box.
        """)
    // Poll rather than exit: under `brew services` (KeepAlive) exiting would
    // spin, and polling means the service starts working the moment it is
    // granted.
    while !isTrusted(prompting: false) {
        Thread.sleep(forTimeInterval: 3)
    }
    log("# Accessibility granted")
}

if opts.check {
    print(isTrusted(prompting: false) ? "trusted" : "not trusted")
    print(URL(fileURLWithPath: CommandLine.arguments[0]).standardizedFileURL.path)
    exit(isTrusted(prompting: false) ? 0 : 1)
}

// MARK: - hidutil

// An event tap sees Caps Lock as a flagsChanged event and can swallow it, but
// the lock state and the LED are owned by IOKit below the tap, so swallowing
// does not stop it toggling. The supported setup is therefore to remap Caps
// Lock to F18 and use that as the toggle key. The mapping does not survive a
// reboot, which is why it is applied here at startup rather than once by hand.
let capsLockUsage = "0x700000039"
let f18Usage = "0x70000006d"

@discardableResult
func hidutil(_ json: String) -> Bool {
    let p = Process()
    p.executableURL = URL(fileURLWithPath: "/usr/bin/hidutil")
    p.arguments = ["property", "--set", json]
    p.standardOutput = FileHandle.nullDevice
    do { try p.run() } catch { return false }
    p.waitUntilExit()
    return p.terminationStatus == 0
}

/// Whether we actually installed a mapping.  `hidutil --set {}` clears *every*
/// user key mapping, not just ours, so a run that never remapped must not
/// "restore" anything -- it would silently discard a mapping the user set.
var remapApplied = false

func applyRemap() {
    guard remapEnabled else { return }
    let json = """
        {"UserKeyMapping":[{"HIDKeyboardModifierMappingSrc":\(capsLockUsage),\
        "HIDKeyboardModifierMappingDst":\(f18Usage)}]}
        """
    if hidutil(json) {
        remapApplied = true
        log("# Caps Lock remapped to F18")
    } else {
        log("# hidutil remap failed; pass --no-remap and pick another --toggle")
    }
}

func clearRemap() {
    guard remapApplied else { return }
    hidutil("{\"UserKeyMapping\":[]}")
    remapApplied = false
}

// MARK: - kanata

// kanata sits *below* this tap: it re-emits through its own virtual device, so
// while it runs the codes arriving here are the ones it produced, not the keys
// that were pressed.  That is the most confusing thing about reading this
// window, which is why turning it off deserves a switch rather than a trip to
// the terminal.
//
// Homebrew installs it as a LaunchDaemon running as root, with KeepAlive set,
// so killing the process achieves nothing -- launchd starts it straight back
// up.  The only honest mechanisms are launchctl's, and in the system domain
// they need root; that is why flipping the switch raises the standard
// authorisation dialog.
enum Kanata {
    struct Service {
        let label: String
        let plist: String
        /// The `system` domain needs root.  A per-user agent does not.
        let domain: String
        var needsAdmin: Bool { domain == "system" }
    }

    private static let searchPaths: [(dir: String, domain: String)] = [
        ("/Library/LaunchDaemons", "system"),
        ("/Library/LaunchAgents", "gui/\(getuid())"),
        (NSHomeDirectory() + "/Library/LaunchAgents", "gui/\(getuid())"),
    ]

    /// Resolved once.  A launchd job is not going to be installed while the
    /// window is open, and scanning three directories at 20 Hz would be rude.
    static let service: Service? = {
        let fm = FileManager.default
        for (dir, domain) in searchPaths {
            guard let names = try? fm.contentsOfDirectory(atPath: dir) else { continue }
            for name in names.sorted()
            where name.hasSuffix(".plist") && name.lowercased().contains("kanata") {
                return Service(label: String(name.dropLast(6)),
                               plist: dir + "/" + name,
                               domain: domain)
            }
        }
        return nil
    }()

    /// Ask about the process, not the job.  `launchctl print` is slower and
    /// needs the right domain to say anything useful, and the question here is
    /// only ever "is something rewriting my keys right now".
    static func isRunning() -> Bool {
        let p = Process()
        p.executableURL = URL(fileURLWithPath: "/usr/bin/pgrep")
        p.arguments = ["-x", "kanata"]
        p.standardOutput = FileHandle.nullDevice
        p.standardError = FileHandle.nullDevice
        do { try p.run() } catch { return false }
        p.waitUntilExit()
        return p.terminationStatus == 0
    }

    /// Stop or start the job, off the main thread.  The authorisation dialog
    /// blocks until it is answered, and the tap callback runs on main under a
    /// deadline CoreGraphics will kill the tap for missing -- so this must not
    /// be done inline no matter how briefly it seems to take.
    static func setEnabled(_ on: Bool, completion: @escaping (String) -> Void) {
        guard let svc = service else {
            completion("no kanata launchd job found; nothing to toggle")
            return
        }
        let cmd = on
            ? "launchctl bootstrap \(svc.domain) '\(svc.plist)'"
            : "launchctl bootout \(svc.domain)/\(svc.label)"
        DispatchQueue.global(qos: .userInitiated).async {
            let result = run(cmd, asAdmin: svc.needsAdmin)
            DispatchQueue.main.async { completion(result) }
        }
    }

    private static func run(_ cmd: String, asAdmin: Bool) -> String {
        let p = Process()
        if asAdmin {
            // osascript raises the system's own authorisation dialog.  The
            // password is typed into that dialog and never passes through this
            // process, which is the whole reason for going via osascript.
            let escaped = cmd.replacingOccurrences(of: "\\", with: "\\\\")
                             .replacingOccurrences(of: "\"", with: "\\\"")
            p.executableURL = URL(fileURLWithPath: "/usr/bin/osascript")
            p.arguments = ["-e", "do shell script \"\(escaped)\" with administrator privileges"]
        } else {
            p.executableURL = URL(fileURLWithPath: "/bin/sh")
            p.arguments = ["-c", cmd]
        }
        let err = Pipe()
        p.standardOutput = FileHandle.nullDevice
        p.standardError = err
        do { try p.run() } catch { return "could not run launchctl: \(error)" }
        let data = err.fileHandleForReading.readDataToEndOfFile()
        p.waitUntilExit()
        if p.terminationStatus == 0 { return "" }
        let msg = String(data: data, encoding: .utf8)?
            .trimmingCharacters(in: .whitespacesAndNewlines) ?? ""
        // -128 is AppleScript for "the user dismissed the dialog".
        if msg.contains("-128") { return "cancelled" }
        return msg.isEmpty ? "launchctl failed (status \(p.terminationStatus))" : msg
    }
}

// MARK: - The machine

let machine = Process()
let toMachine = Pipe()
let fromMachine = Pipe()
let writeLock = NSLock()

func startMachine() {
    machine.executableURL = URL(fileURLWithPath: opts.binary)
    machine.arguments = ["run", "--wire", "quartz", "--platform", "mac", "--toggle", currentToggle]
    if opts.monitor { machine.arguments?.append("--monitor") }
    machine.standardInput = toMachine
    machine.standardOutput = fromMachine
    // Lean reports unparseable lines on stderr; in the GUI that is worth seeing
    // rather than leaving on a terminal nobody is looking at.
    if opts.monitor {
        machine.standardError = machineErr
        Thread.detachNewThread {
            let h = machineErr.fileHandleForReading
            while true {
                let chunk = h.availableData
                if chunk.isEmpty { break }
                if let s = String(data: chunk, encoding: .utf8) {
                    for l in s.split(separator: "\n") { logBuffer.append(String(l)) }
                }
            }
        }
    }
    machine.terminationHandler = { p in
        log("# capslockmode exited (\(p.terminationStatus)); stopping")
        // Headless, dying with the child is right: something else supervises us.
        // With a window open it is not -- disarm, restore the keyboard, and stay
        // up so the reason is still on screen. A Lean panic aborts, and `atexit`
        // does not run on abort, so this is the only path that restores the
        // remap in that case.
        if opts.monitor {
            DispatchQueue.main.async { monitorUI?.childDied(status: p.terminationStatus) }
        } else {
            clearRemap()
            exit(1)
        }
    }
    do {
        try machine.run()
    } catch {
        log("# cannot start \(opts.binary): \(error)")
        exit(1)
    }
}

func sendLine(_ line: String) {
    writeLock.lock()
    defer { writeLock.unlock() }
    if let data = (line + "\n").data(using: .utf8) {
        toMachine.fileHandleForWriting.write(data)
    }
}

/// From the tap, so it counts towards the liveness number.
func send(_ line: String) {
    writeLock.lock()
    eventsSeen += 1
    writeLock.unlock()
    sendLine(line)
}

/// Rebind the modal key on a running machine.  Lean resets its state when it
/// accepts this, so it cannot strand you in normal mode with no way out.
func applyToggle(_ k: String) {
    currentToggle = k
    if machineStarted { sendLine("toggle \(k)") }
}

// MARK: - Flags

func flagNames(_ flags: CGEventFlags) -> String {
    var parts: [String] = []
    if flags.contains(.maskControl) { parts.append("ctrl") }
    if flags.contains(.maskAlternate) { parts.append("alt") }
    if flags.contains(.maskShift) { parts.append("shift") }
    if flags.contains(.maskCommand) { parts.append("command") }
    return parts.isEmpty ? "-" : parts.joined(separator: ",")
}

func parseFlags(_ s: String) -> CGEventFlags {
    var flags: CGEventFlags = []
    if s == "-" { return flags }
    for part in s.split(separator: ",") {
        switch part {
        case "ctrl": flags.insert(.maskControl)
        case "alt": flags.insert(.maskAlternate)
        case "shift": flags.insert(.maskShift)
        case "command": flags.insert(.maskCommand)
        default: break
        }
    }
    return flags
}

// MARK: - Injection

// Our own events carry a signature, because a tap observes what it posts. The
// Lean side proves the machine ignores anything marked this way
// (`CapslockMode.no_feedback`); the callback below never even forwards it.
let signature: Int64 = 0x434C_4D44   // "CLMD"
let eventSource = CGEventSource(stateID: .hidSystemState)

func inject(_ line: String) {
    let parts = line.split(separator: " ").map(String.init)
    guard let kind = parts.first else { return }
    if kind == "flags" { return }   // flags ride on the key events themselves
    guard parts.count >= 3 else { return }
    let down = parts[1] == "down"
    let flags = parts.count > 3 ? parseFlags(parts[3]) : []

    if opts.dryRun {
        print("inject \(line)")
        return
    }

    switch kind {
    case "key":
        guard let code = UInt16(parts[2]),
              let event = CGEvent(keyboardEventSource: eventSource,
                                  virtualKey: CGKeyCode(code), keyDown: down) else { return }
        event.flags = flags
        event.setIntegerValueField(.eventSourceUserData, value: signature)
        event.post(tap: .cghidEventTap)
    case "text":
        // A character with no virtual keycode on this layout: type it directly.
        //
        // The payload is a Unicode scalar in decimal, not the character, because
        // this line is split on spaces and framed by newlines -- a raw ' ' would
        // shift every field left and a raw '\n' would end the line early.
        // `Quartz.charCode` is the matching half on the Lean side.
        guard let v = UInt32(parts[2]), let ch = Unicode.Scalar(v),
              let event = CGEvent(keyboardEventSource: eventSource,
                                  virtualKey: 0, keyDown: down) else { return }
        var utf16 = Array(String(Character(ch)).utf16)
        event.keyboardSetUnicodeString(stringLength: utf16.count, unicodeString: &utf16)
        event.flags = flags
        event.setIntegerValueField(.eventSourceUserData, value: signature)
        event.post(tap: .cghidEventTap)
    default:
        break
    }
}

func readLoop() {
    let handle = fromMachine.fileHandleForReading
    var buffer = Data()
    while true {
        let chunk = handle.availableData
        if chunk.isEmpty { break }
        buffer.append(chunk)
        while let nl = buffer.firstIndex(of: 0x0A) {
            let lineData = buffer[buffer.startIndex..<nl]
            buffer = buffer[buffer.index(after: nl)...]
            guard let line = String(data: lineData, encoding: .utf8) else { continue }
            let trimmed = line.trimmingCharacters(in: .whitespaces)
            // Monitor lines share this stream with injectable events and are told
            // apart by prefix alone. They must be routed before the `#` check,
            // which drops everything it does not recognise.
            if trimmed.hasPrefix("mon ") {
                logBuffer.accept(String(trimmed.dropFirst(4)))
                continue
            }
            if trimmed.isEmpty || trimmed.hasPrefix("#") { continue }
            inject(trimmed)
        }
    }
}

// MARK: - The tap

// The callback is a C function pointer and cannot capture, so the tap lives in
// a global for the re-enable path.
var eventTap: CFMachPort?

let callback: CGEventTapCallBack = { _, type, event, _ in
    switch type {
    case .tapDisabledByTimeout, .tapDisabledByUserInput:
        // A tap that is too slow gets switched off; switch it back on.
        if let tap = eventTap { CGEvent.tapEnable(tap: tap, enable: true) }
        return nil
    case .keyDown, .keyUp, .flagsChanged:
        if event.getIntegerValueField(.eventSourceUserData) == signature {
            return Unmanaged.passUnretained(event)   // ours: hands off
        }
        // Copy the device fields onto the wire and let the machine decide what
        // they mean. Deliberately unconditional rather than "only when it
        // changes": keeping the comparison here would put state and policy in
        // the platform layer, and one extra pipe write is microseconds against
        // the tap's millisecond deadline. `sendLine`, not `send`, so a
        // diagnostic is not counted as an intercepted event.
        if opts.monitor {
            sendLine("dev \(event.getIntegerValueField(.keyboardEventKeyboardType)) "
                     + "\(event.getIntegerValueField(.eventSourceUnixProcessID))")
        }
        let flags = flagNames(event.flags)
        if type == .flagsChanged {
            send("flags \(flags)")
        } else {
            let code = event.getIntegerValueField(.keyboardEventKeycode)
            send("\(type == .keyDown ? "down" : "up") \(code) \(flags)")
        }
        // Everything is swallowed and replayed by the reader thread, which is
        // what keeps the callback off the pipe's round trip.
        //
        // This was long assumed to cost key repeat, on the grounds that a
        // posted event does not auto-repeat. That reasoning is about the wrong
        // link. Auto-repeat is generated upstream of a session tap -- by the
        // window server, or by another remapper like kanata -- and swallowing
        // an event here tells that generator nothing. So the repeats keep
        // arriving as ordinary events and each one is handled normally.
        // Observed working with kanata upstream; a bare keyboard is expected to
        // behave the same way for the same reason, but has not been checked.
        return nil
    default:
        return Unmanaged.passUnretained(event)
    }
}

// MARK: - Arming
//
// Arming is the dangerous half: from here on every keystroke in the session is
// swallowed and only comes back if the machine answers. It is therefore its own
// step, so a window can open and prove itself before anything is at risk.

var tapSource: CFRunLoopSource?
var machineStarted = false
var armed = false

func armTap() -> Bool {
    let mask = (1 << CGEventType.keyDown.rawValue)
             | (1 << CGEventType.keyUp.rawValue)
             | (1 << CGEventType.flagsChanged.rawValue)

    guard let tap = CGEvent.tapCreate(tap: .cgSessionEventTap,
                                      place: .headInsertEventTap,
                                      options: .defaultTap,
                                      eventsOfInterest: CGEventMask(mask),
                                      callback: callback,
                                      userInfo: nil) else {
        log("# could not create the event tap (Accessibility permission?)")
        return false
    }
    eventTap = tap
    let source = CFMachPortCreateRunLoopSource(kCFAllocatorDefault, tap, 0)
    tapSource = source
    CFRunLoopAddSource(CFRunLoopGetCurrent(), source, .commonModes)
    CGEvent.tapEnable(tap: tap, enable: true)
    return true
}

func disarmTap() {
    if let tap = eventTap {
        CGEvent.tapEnable(tap: tap, enable: false)
        if let source = tapSource {
            CFRunLoopRemoveSource(CFRunLoopGetCurrent(), source, .commonModes)
        }
        CFMachPortInvalidate(tap)
    }
    tapSource = nil
    eventTap = nil
}

/// Take the keyboard.  The machine is started once and kept: it reads nothing
/// while the tap is off, so disarming does not need to kill it.
func arm() -> Bool {
    applyRemap()
    if !machineStarted {
        startMachine()
        machineStarted = true
        Thread.detachNewThread(readLoop)
    }
    guard armTap() else {
        clearRemap()
        return false
    }
    armed = true
    log("# armed (toggle: \(currentToggle))")
    return true
}

/// Give the keyboard back, without quitting.
func disarm() {
    guard armed else { return }
    disarmTap()
    clearRemap()
    armed = false
    log("# disarmed; keyboard restored")
}

/// The only way out.  `terminationHandler` has to be cleared first or killing
/// the child re-enters it and reports a deliberate quit as a failure.
func quitCleanly() -> Never {
    disarm()
    machine.terminationHandler = nil
    if machineStarted && machine.isRunning { machine.terminate() }
    exit(0)
}

// MARK: - The window

final class MonitorWindow: NSObject, NSWindowDelegate, NSApplicationDelegate {
    private let window: NSWindow
    private let textView: NSTextView
    private let stateField: NSTextField
    private let statusField: NSTextField
    private let armButton: NSButton
    private let toggleField: NSTextField
    private let remapBox: NSButton
    private let font = NSFont.monospacedSystemFont(ofSize: 11, weight: .regular)
    private var timer: Timer?
    private var lines: [String] = []
    private let maxLines = 4000
    /// Asking TCC whether we are trusted is a real lookup; the drain runs at
    /// 20 Hz and does not need the answer that often.
    private var trusted = false
    private var trustChecked = Date.distantPast
    private let accessButton = NSButton(title: "Accessibility...", target: nil, action: nil)
    private let kanataBox: NSButton
    /// Same reasoning as `trusted`: a `pgrep` per frame is wasteful, and the
    /// answer does not change on that timescale.
    private var kanataRunning = false
    private var kanataChecked = Date.distantPast
    /// While a toggle is in flight the poll must not fight the user's click.
    private var kanataBusy = false

    override init() {
        window = NSWindow(contentRect: NSRect(x: 0, y: 0, width: 880, height: 560),
                          styleMask: [.titled, .closable, .miniaturizable, .resizable],
                          backing: .buffered, defer: false)
        window.title = "CapslockMode monitor"

        let content = window.contentView!
        let w = content.bounds.width, h = content.bounds.height

        statusField = NSTextField(labelWithString: "")
        statusField.frame = NSRect(x: 12, y: h - 30, width: w - 130, height: 18)
        statusField.autoresizingMask = [.width, .minYMargin]

        stateField = NSTextField(labelWithString: "")
        stateField.frame = NSRect(x: 12, y: h - 52, width: w - 130, height: 18)
        stateField.font = NSFont.monospacedSystemFont(ofSize: 12, weight: .medium)
        stateField.autoresizingMask = [.width, .minYMargin]

        armButton = NSButton(title: "Start", target: nil, action: nil)
        armButton.bezelStyle = .rounded
        armButton.frame = NSRect(x: w - 108, y: h - 44, width: 96, height: 30)
        armButton.autoresizingMask = [.minXMargin, .minYMargin]

        toggleField = NSTextField(string: currentToggle)
        toggleField.frame = NSRect(x: 84, y: h - 80, width: 90, height: 22)
        toggleField.autoresizingMask = [.minYMargin]

        remapBox = NSButton(checkboxWithTitle: "Remap Caps Lock to F18 (hidutil)",
                            target: nil, action: nil)
        remapBox.frame = NSRect(x: 190, y: h - 78, width: 300, height: 20)
        remapBox.state = remapEnabled ? .on : .off
        remapBox.autoresizingMask = [.minYMargin]

        kanataBox = NSButton(checkboxWithTitle: "kanata", target: nil, action: nil)
        kanataBox.frame = NSRect(x: 500, y: h - 78, width: 264, height: 20)
        kanataBox.autoresizingMask = [.minYMargin]

        accessButton.bezelStyle = .rounded
        accessButton.frame = NSRect(x: w - 108, y: h - 78, width: 96, height: 24)
        accessButton.autoresizingMask = [.minXMargin, .minYMargin]

        let toggleLabel = NSTextField(labelWithString: "Modal key:")
        toggleLabel.frame = NSRect(x: 12, y: h - 77, width: 70, height: 18)
        toggleLabel.autoresizingMask = [.minYMargin]

        let scroll = NSScrollView(frame: NSRect(x: 0, y: 0, width: w, height: h - 92))
        scroll.hasVerticalScroller = true
        scroll.autoresizingMask = [.width, .height]
        scroll.borderType = .noBorder

        textView = NSTextView(frame: scroll.contentView.bounds)
        textView.isEditable = false
        textView.isRichText = false
        textView.font = font
        textView.autoresizingMask = [.width]
        textView.isVerticallyResizable = true
        textView.textContainer?.widthTracksTextView = true
        scroll.documentView = textView

        super.init()

        armButton.target = self
        armButton.action = #selector(toggleArm)
        toggleField.target = self
        toggleField.action = #selector(toggleKeyChanged)
        remapBox.target = self
        remapBox.action = #selector(remapChanged)
        kanataBox.target = self
        kanataBox.action = #selector(kanataChanged)
        accessButton.target = self
        accessButton.action = #selector(openAccessibility)
        content.addSubview(statusField)
        content.addSubview(stateField)
        content.addSubview(armButton)
        content.addSubview(toggleLabel)
        content.addSubview(toggleField)
        content.addSubview(remapBox)
        content.addSubview(kanataBox)
        content.addSubview(accessButton)
        content.addSubview(scroll)
        window.delegate = self
        window.center()
    }

    func present() {
        refreshStatus()
        stateField.stringValue = "machine: not started"
        append(["Disarmed. Nothing is intercepted yet.",
                "Press Start to install the event tap.",
                "",
                "If another remapper (kanata, Karabiner) already owns Caps Lock,",
                "untick the remap and set Modal key to something it passes through",
                "-- f13..f20 are the usual spares. Every key you press shows up",
                "below under `key`, so you can arm, look, and rebind.",
                ""])
        window.makeKeyAndOrderFront(nil)
        let t = Timer.scheduledTimer(withTimeInterval: 0.05, repeats: true) { [weak self] _ in
            self?.tick()
        }
        RunLoop.main.add(t, forMode: .common)
        timer = t
    }

    /// Drain whatever the producers left, at a rate the window can draw.
    private func tick() {
        let (new, state, dropped) = logBuffer.drain()
        if dropped > 0 { append(["... \(dropped) lines dropped ..."]) }
        if !new.isEmpty { append(new) }
        if let state = state { stateField.stringValue = "mode: \(state)" }
        refreshStatus()
    }

    private func refreshStatus() {
        if Date().timeIntervalSince(trustChecked) > 1.0 {
            let now = isTrusted(prompting: false)
            // A grant can be revoked, or go stale because the binary was
            // rebuilt, while we are running. If that happens while armed the
            // tap is already dead, so give the keyboard back rather than
            // sitting there swallowing keys that will never come back.
            if armed && !now && trusted {
                append(["", "Accessibility was lost. Disarming so the keyboard keeps working.", ""])
                disarm()
            }
            trusted = now
            trustChecked = Date()
        }
        refreshKanata()
        let trust = trusted ? "granted" : "NOT granted"
        let state = armed ? "ARMED - keystrokes are being intercepted" : "disarmed"
        statusField.stringValue = "\(state)   |   Accessibility: \(trust)   |   events seen: \(eventsSeen)"
        armButton.title = armed ? "Stop" : "Start"
        accessButton.isHidden = trusted
    }

    /// kanata's state is polled rather than watched: there is no notification
    /// for "a launchd job went away", and three seconds is well inside the time
    /// it takes to wonder why the codes look wrong.
    private func refreshKanata() {
        guard !kanataBusy else { return }
        guard Date().timeIntervalSince(kanataChecked) > 3.0 else { return }
        kanataRunning = Kanata.isRunning()
        kanataChecked = Date()
        kanataBox.state = kanataRunning ? .on : .off
        if Kanata.service == nil && !kanataRunning {
            kanataBox.title = "kanata: not installed"
            kanataBox.isEnabled = false
        } else {
            kanataBox.isEnabled = true
            kanataBox.title = kanataRunning ? "kanata: running" : "kanata: stopped"
        }
    }

    /// Stopping kanata is not cosmetic: it changes which device the codes below
    /// arrive from, so say so rather than letting the window quietly start
    /// describing a different keyboard.
    @objc func kanataChanged() {
        let wanted = kanataBox.state == .on
        guard let svc = Kanata.service else {
            append(["No kanata launchd job found, so there is nothing to toggle.",
                    "If you start kanata by hand, stop it the way you started it."])
            kanataBox.state = kanataRunning ? .on : .off
            return
        }
        kanataBusy = true
        kanataBox.isEnabled = false
        kanataBox.title = wanted ? "kanata: starting..." : "kanata: stopping..."
        append([(wanted ? "starting " : "stopping ") + svc.label
                + " in domain " + svc.domain
                + (svc.needsAdmin ? " (asks for an administrator password)" : "")])
        if armed {
            append(["kanata is changing under an armed tap: the codes below will",
                    "start arriving from a different device. Stop and Start again",
                    "if what you see stops making sense."])
        }
        Kanata.setEnabled(wanted) { [weak self] err in
            guard let self = self else { return }
            self.kanataBusy = false
            self.kanataBox.isEnabled = true
            self.kanataChecked = .distantPast
            if err == "cancelled" {
                self.append(["authorisation cancelled; kanata left as it was"])
            } else if !err.isEmpty {
                self.append(["kanata: " + err])
            } else {
                self.append(["kanata " + (wanted ? "started" : "stopped")])
            }
        }
    }

    /// The grant is keyed to this binary's code identity, and an ad-hoc signed
    /// binary gets a new one every rebuild -- so a stale entry looks present and
    /// ticked while doing nothing. Re-ticking it does not help; it has to be
    /// removed and re-added.
    @objc func openAccessibility() {
        let path = URL(fileURLWithPath: CommandLine.arguments[0]).standardizedFileURL.path
        append(["", "Add this exact path under Privacy & Security -> Accessibility:",
                "  " + path,
                "If an entry for capslockmode-quartz is already there, REMOVE it first:",
                "a rebuilt binary has a new identity and the old entry is dead.", ""])
        NSWorkspace.shared.open(
            URL(string: "x-apple.systempreferences:com.apple.preference.security?Privacy_Accessibility")!)
    }

    private func append(_ new: [String]) {
        lines.append(contentsOf: new)
        if lines.count > maxLines {
            // Infrequent bulk trim rather than a per-line shuffle.
            lines.removeFirst(lines.count - maxLines)
            textView.string = lines.joined(separator: "\n") + "\n"
        } else {
            let chunk = new.joined(separator: "\n") + "\n"
            textView.textStorage?.append(NSAttributedString(
                string: chunk, attributes: [.font: font, .foregroundColor: NSColor.textColor]))
        }
        textView.scrollToEndOfDocument(nil)
    }

    @objc func toggleArm() {
        if armed {
            disarm()
        } else {
            guard isTrusted(prompting: true) else {
                append(["Accessibility permission is needed before the tap can be installed.",
                        "Add this binary under System Settings -> Privacy & Security -> Accessibility:",
                        "  " + URL(fileURLWithPath: CommandLine.arguments[0]).standardizedFileURL.path,
                        "Then press Start again.", ""])
                refreshStatus()
                return
            }
            if !arm() {
                append(["Could not arm. The tap was refused; nothing is intercepted.", ""])
            }
        }
        refreshStatus()
    }

    /// Enter in the key field, or losing focus, rebinds.  Takes effect on a
    /// running machine immediately, so you can hunt for a key that your other
    /// remapper lets through without disarming.
    @objc func toggleKeyChanged() {
        let k = toggleField.stringValue.trimmingCharacters(in: .whitespaces)
        guard !k.isEmpty else {
            toggleField.stringValue = currentToggle
            return
        }
        applyToggle(k)
        append(["modal key set to \(k)\(machineStarted ? "" : " (applies when armed)")"])
    }

    @objc func remapChanged() {
        remapEnabled = (remapBox.state == .on)
        if armed {
            // Apply now rather than at the next arm, so the checkbox means what
            // it says while the tap is live.
            if remapEnabled { applyRemap() } else { clearRemap() }
        }
        append(["Caps Lock remap \(remapEnabled ? "enabled" : "disabled")"])
    }

    func childDied(status: Int32) {
        disarm()
        append(["", "The machine exited (status \(status)). Disarmed; your keyboard is back.", ""])
        stateField.stringValue = "machine: exited (\(status))"
        refreshStatus()
    }

    /// The red button. It is the escape hatch for a wedged keyboard, so it does
    /// the full teardown rather than just closing a window.
    func windowShouldClose(_ sender: NSWindow) -> Bool {
        quitCleanly()
    }

    @objc func quitNow() {
        quitCleanly()
    }

    func applicationShouldTerminateAfterLastWindowClosed(_ s: NSApplication) -> Bool { true }
}

var monitorUI: MonitorWindow?

// MARK: - Main

for sig in [SIGINT, SIGTERM] {
    signal(sig) { _ in
        clearRemap()
        exit(0)
    }
}
atexit { clearRemap() }

if opts.monitor {
    let app = NSApplication.shared
    // Without this a binary with no bundle gets `.prohibited`: no Dock icon, no
    // focus, and no window ever appears.
    app.setActivationPolicy(.regular)

    let ui = MonitorWindow()
    monitorUI = ui
    app.delegate = ui

    // A minimal menu, purely so Cmd-Q exists as a second way out.
    let menu = NSMenu()
    let appItem = NSMenuItem()
    let appMenu = NSMenu()
    appMenu.addItem(withTitle: "Quit CapslockMode monitor",
                    action: #selector(MonitorWindow.quitNow), keyEquivalent: "q")
    appMenu.items.forEach { $0.target = ui }
    appItem.submenu = appMenu
    menu.addItem(appItem)
    app.mainMenu = menu

    ui.present()
    app.activate(ignoringOtherApps: true)
    app.run()
} else {
    // Headless: unchanged behaviour, for `brew services`.
    waitForTrust()
    guard arm() else {
        clearRemap()
        exit(1)
    }
    log("# capslockmode-quartz running (toggle: \(currentToggle))")
    CFRunLoopRun()
}
