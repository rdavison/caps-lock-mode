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

// MARK: - Options

struct Options {
    var binary = "./capslockmode"
    var toggle = "f18"
    var remap = true
    var dryRun = false
    var check = false
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
        case "--help", "-h":
            print("""
            capslockmode-quartz - macOS keyboard driver for CapslockMode

              --binary <path>   the capslockmode executable (or set CAPSLOCKMODE_BIN)
              --toggle <key>    key that switches modes (default: f18, see --no-remap)
              --no-remap        do not remap Caps Lock to F18 with hidutil
              --dry-run         print what would be injected instead of injecting it
              --check           report Accessibility permission status and exit
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
    return o
}

let opts = parseArgs()

func log(_ s: String) {
    FileHandle.standardError.write("\(s)\n".data(using: .utf8)!)
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

func applyRemap() {
    guard opts.remap else { return }
    let json = """
        {"UserKeyMapping":[{"HIDKeyboardModifierMappingSrc":\(capsLockUsage),\
        "HIDKeyboardModifierMappingDst":\(f18Usage)}]}
        """
    if hidutil(json) { log("# Caps Lock remapped to F18") }
    else { log("# hidutil remap failed; pass --no-remap and pick another --toggle") }
}

func clearRemap() {
    guard opts.remap else { return }
    hidutil("{\"UserKeyMapping\":[]}")
}

// MARK: - The machine

let machine = Process()
let toMachine = Pipe()
let fromMachine = Pipe()
let writeLock = NSLock()

func startMachine() {
    machine.executableURL = URL(fileURLWithPath: opts.binary)
    machine.arguments = ["run", "--wire", "quartz", "--platform", "mac", "--toggle", opts.toggle]
    machine.standardInput = toMachine
    machine.standardOutput = fromMachine
    machine.terminationHandler = { p in
        log("# capslockmode exited (\(p.terminationStatus)); stopping")
        clearRemap()
        exit(1)
    }
    do {
        try machine.run()
    } catch {
        log("# cannot start \(opts.binary): \(error)")
        exit(1)
    }
}

func send(_ line: String) {
    writeLock.lock()
    defer { writeLock.unlock() }
    if let data = (line + "\n").data(using: .utf8) {
        toMachine.fileHandleForWriting.write(data)
    }
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
        // a character with no virtual keycode on this layout: type it directly
        guard let ch = parts[2].unicodeScalars.first,
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
        // The cost is key repeat: the original event is gone, and a posted
        // event does not auto-repeat, so holding a key down types it once.
        // Fixing that means waiting for the machine's answer inside the
        // callback and returning the original event when it is a pass-through
        // -- a synchronous round trip, with the tap's deadline to respect.
        return nil
    default:
        return Unmanaged.passUnretained(event)
    }
}

// MARK: - Main

waitForTrust()
applyRemap()
startMachine()

for sig in [SIGINT, SIGTERM] {
    signal(sig) { _ in
        clearRemap()
        exit(0)
    }
}
atexit { clearRemap() }

Thread.detachNewThread(readLoop)

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
    clearRemap()
    exit(1)
}
eventTap = tap

let runLoopSource = CFMachPortCreateRunLoopSource(kCFAllocatorDefault, tap, 0)
CFRunLoopAddSource(CFRunLoopGetCurrent(), runLoopSource, .commonModes)
CGEvent.tapEnable(tap: tap, enable: true)
log("# capslockmode-quartz running (toggle: \(opts.toggle))")
CFRunLoopRun()
