// Watch raw HID keyboard usages, without taking the keyboard from anyone.
//
//     swiftc -O drivers/hid_listen.swift -o .lake/build/bin/capslockmode-hidlisten
//     ./.lake/build/bin/capslockmode-hidlisten
//
// This is a diagnostic, not a driver. It opens matching keyboards with
// `kIOHIDOptionsTypeNone` -- *not* `kIOHIDOptionsTypeSeizeDevice` -- so it only
// observes. It never grabs a device, never suppresses a key, and never injects
// anything. Running it cannot break your keyboard.
//
// Why it exists: an event tap sees keystrokes only after every lower layer has
// finished with them. When something like kanata or Karabiner sits below, it
// grabs the real keyboard and re-emits through a virtual HID device, so by the
// time a tap sees an event the original key is gone -- press `s`, observe `i`.
// This listens one layer down and prints the device each usage came from, which
// is the only way to tell "the layer below swallowed it" from "it arrived and we
// could not name it".
//
// The open question it answers: whether a *non-seizing* observer still receives
// values from a device another process has seized. If the physical keyboard
// shows up here while kanata is running, the answer is yes.
//
// Needs Input Monitoring (System Settings -> Privacy & Security -> Input
// Monitoring). That is a different permission from Accessibility, and it is
// pinned to this binary's path like all TCC grants.

import Foundation
import IOKit
import IOKit.hid

// MARK: - Naming

/// HID keyboard/keypad page.
let kbPage: UInt32 = 0x07

func deviceName(_ device: IOHIDDevice) -> String {
    func str(_ key: String) -> String? {
        IOHIDDeviceGetProperty(device, key as CFString) as? String
    }
    func num(_ key: String) -> Int? {
        (IOHIDDeviceGetProperty(device, key as CFString) as? NSNumber)?.intValue
    }
    let product = str(kIOHIDProductKey) ?? "unknown"
    let vendor = num(kIOHIDVendorIDKey) ?? 0
    let pid = num(kIOHIDProductIDKey) ?? 0
    return String(format: "%@ (vid %04x pid %04x)", product, vendor, pid)
}

/// Only the usages a keyboard actually reports as keys; a keyboard also emits
/// LED and consumer elements we do not care about here.
func isKeyUsage(_ page: UInt32, _ usage: UInt32) -> Bool {
    page == kbPage && usage >= 0x04 && usage <= 0xE7
}

// MARK: - State

var seenDevices: [String: Int] = [:]
var total = 0
let start = Date()

func stamp() -> String {
    String(format: "%7.3f", Date().timeIntervalSince(start))
}

// MARK: - Callback

let onValue: IOHIDValueCallback = { _, _, _, value in
    let element = IOHIDValueGetElement(value)
    let page = IOHIDElementGetUsagePage(element)
    let usage = IOHIDElementGetUsage(element)
    guard isKeyUsage(page, usage) else { return }

    let pressed = IOHIDValueGetIntegerValue(value)
    let device = IOHIDElementGetDevice(element)
    let name = deviceName(device)

    total += 1
    if seenDevices[name] == nil {
        seenDevices[name] = 0
        print("\n== new device: \(name)\n")
    }
    seenDevices[name]! += 1

    // Usage 0x39 is Caps Lock. Worth marking, because an event tap cannot
    // intercept it at all -- if it shows up here, a HID-level driver could.
    let note = usage == 0x39 ? "   <- Caps Lock, invisible to an event tap" : ""
    print("\(stamp())  \(pressed != 0 ? "down" : "up  ")  "
          + String(format: "page %02x usage %02x", page, usage)
          + "  \(name)\(note)")
}

// MARK: - Main

let manager = IOHIDManagerCreate(kCFAllocatorDefault, IOOptionBits(kIOHIDOptionsTypeNone))

// Match anything that calls itself a keyboard, on either of the two usages a
// keyboard can advertise.
let matches: [[String: Any]] = [
    [kIOHIDDeviceUsagePageKey as String: kHIDPage_GenericDesktop,
     kIOHIDDeviceUsageKey as String: kHIDUsage_GD_Keyboard],
    [kIOHIDDeviceUsagePageKey as String: kHIDPage_GenericDesktop,
     kIOHIDDeviceUsageKey as String: kHIDUsage_GD_Keypad],
]
IOHIDManagerSetDeviceMatchingMultiple(manager, matches as CFArray)
IOHIDManagerRegisterInputValueCallback(manager, onValue, nil)
IOHIDManagerScheduleWithRunLoop(manager, CFRunLoopGetCurrent(), CFRunLoopMode.defaultMode.rawValue)

// Open each device on its own rather than through IOHIDManagerOpen, which
// opens everything and fails on the first refusal. Per-device tells us *which*
// keyboard is grabbed and whether any others can still be watched -- a far more
// useful answer than one error code for the whole set.
let devices = (IOHIDManagerCopyDevices(manager) as? Set<IOHIDDevice>) ?? []
print("matched \(devices.count) keyboard device(s):\n")

var opened = 0
var seized: [String] = []
var denied = false

for d in devices.sorted(by: { deviceName($0) < deviceName($1) }) {
    // kIOHIDOptionsTypeNone: observe, do not seize. This is what makes the
    // probe safe to run alongside whatever already owns the keyboard.
    let rc = IOHIDDeviceOpen(d, IOOptionBits(kIOHIDOptionsTypeNone))
    switch rc {
    case kIOReturnSuccess:
        opened += 1
        print("  watching   \(deviceName(d))")
    case kIOReturnExclusiveAccess:
        seized.append(deviceName(d))
        print("  SEIZED     \(deviceName(d))")
    case kIOReturnNotPermitted, kIOReturnNotPrivileged:
        denied = true
        print("  no access  \(deviceName(d))")
    default:
        print(String(format: "  failed 0x%08x  ", rc) + deviceName(d))
    }
}

if denied {
    FileHandle.standardError.write("""

        Input Monitoring is not granted for this binary.
        Add it under System Settings -> Privacy & Security -> Input Monitoring:
          \(URL(fileURLWithPath: CommandLine.arguments[0]).standardizedFileURL.path)
        The grant is pinned to the path, so a rebuilt or moved binary needs
        removing and re-adding.

        """.data(using: .utf8)!)
}

if !seized.isEmpty {
    print("""

        \(seized.count) device(s) are held exclusively by another process.
        A seized device is invisible even to a passive observer, so those keys
        cannot be seen from here at all -- only the process holding them (kanata,
        Karabiner) sees them. Stopping that process is the only way to watch
        those keys, and then you would be seizing them yourself.
        """)
}

if opened == 0 {
    print("\nNothing to watch. Exiting.")
    exit(1)
}

print("\nlistening on \(opened) device(s), observe only. Ctrl-C to stop.")
print("\nIf the physical keyboard appears below while another remapper is")
print("running, a non-seizing observer can see past it. If only a virtual")
print("device appears, it cannot.\n")

// Report what was seen on the way out, so a short run still says something.
signal(SIGINT) { _ in
    print("\n\n-- summary --")
    for (name, n) in seenDevices.sorted(by: { $0.value > $1.value }) {
        print("  \(n) events  \(name)")
    }
    if seenDevices.isEmpty {
        print("  no key events seen at all")
    }
    exit(0)
}

CFRunLoopRun()
