#!/usr/bin/env python3
"""
Connect a real Linux keyboard to the CapslockMode machine.

    sudo ./drivers/evdev_bridge.py --binary ./.lake/build/bin/capslockmode

The bridge does the three things that need privileges and a platform, and
nothing else:

  1. grab an input device exclusively, so the original keystrokes never reach
     applications;
  2. hand every event to `capslockmode run` over the line protocol;
  3. replay whatever comes back through a virtual uinput keyboard.

All the policy — what `dd` means, when Caps Lock flips a mode — lives in the
Lean program.  This file is deliberately dumb.

Requires: python3-evdev, and write access to /dev/uinput (i.e. root, or a udev
rule).  Try `--dry-run` first: it prints what would be injected instead of
injecting it, and needs no privileges beyond reading the device.
"""
import argparse
import os
import re
import selectors
import subprocess
import sys
import threading

try:
    from evdev import InputDevice, UInput, categorize, ecodes, list_devices
except ImportError:  # pragma: no cover - dependency hint
    sys.exit("python-evdev is required:  pip install evdev")

# --- the US layout, as a table -------------------------------------------------
# CapslockMode wants the *character* a key produces, because that is what makes
# it layout independent.  Translating scan codes into characters is therefore
# the driver's job; swap this table out for another layout.
PLAIN = {
    "KEY_A": "a", "KEY_B": "b", "KEY_C": "c", "KEY_D": "d", "KEY_E": "e",
    "KEY_F": "f", "KEY_G": "g", "KEY_H": "h", "KEY_I": "i", "KEY_J": "j",
    "KEY_K": "k", "KEY_L": "l", "KEY_M": "m", "KEY_N": "n", "KEY_O": "o",
    "KEY_P": "p", "KEY_Q": "q", "KEY_R": "r", "KEY_S": "s", "KEY_T": "t",
    "KEY_U": "u", "KEY_V": "v", "KEY_W": "w", "KEY_X": "x", "KEY_Y": "y",
    "KEY_Z": "z",
    "KEY_1": "1", "KEY_2": "2", "KEY_3": "3", "KEY_4": "4", "KEY_5": "5",
    "KEY_6": "6", "KEY_7": "7", "KEY_8": "8", "KEY_9": "9", "KEY_0": "0",
    "KEY_MINUS": "-", "KEY_EQUAL": "=", "KEY_LEFTBRACE": "[",
    "KEY_RIGHTBRACE": "]", "KEY_BACKSLASH": "\\", "KEY_SEMICOLON": ";",
    "KEY_APOSTROPHE": "'", "KEY_GRAVE": "`", "KEY_COMMA": ",", "KEY_DOT": ".",
    "KEY_SLASH": "/",
}
SHIFTED = {
    "KEY_1": "!", "KEY_2": "@", "KEY_3": "#", "KEY_4": "$", "KEY_5": "%",
    "KEY_6": "^", "KEY_7": "&", "KEY_8": "*", "KEY_9": "(", "KEY_0": ")",
    "KEY_MINUS": "_", "KEY_EQUAL": "+", "KEY_LEFTBRACE": "{",
    "KEY_RIGHTBRACE": "}", "KEY_BACKSLASH": "|", "KEY_SEMICOLON": ":",
    "KEY_APOSTROPHE": '"', "KEY_GRAVE": "~", "KEY_COMMA": "<", "KEY_DOT": ">",
    "KEY_SLASH": "?",
}
NAMED = {
    "KEY_ESC": "esc", "KEY_TAB": "tab", "KEY_ENTER": "enter",
    "KEY_BACKSPACE": "bs", "KEY_DELETE": "del", "KEY_SPACE": "space",
    "KEY_LEFT": "left", "KEY_RIGHT": "right", "KEY_UP": "up",
    "KEY_DOWN": "down", "KEY_HOME": "home", "KEY_END": "end",
    "KEY_PAGEUP": "pgup", "KEY_PAGEDOWN": "pgdn", "KEY_CAPSLOCK": "caps",
    "KEY_LEFTSHIFT": "shift", "KEY_RIGHTSHIFT": "shift",
    "KEY_LEFTCTRL": "ctrl", "KEY_RIGHTCTRL": "ctrl",
    "KEY_LEFTALT": "alt", "KEY_RIGHTALT": "alt",
    "KEY_LEFTMETA": "super", "KEY_RIGHTMETA": "super",
}
NAMED.update({f"KEY_F{i}": f"f{i}" for i in range(1, 25)})

MODIFIER_KEYS = {"shift", "ctrl", "alt", "super"}

# The reverse direction: protocol name -> the scan code to inject.
TO_CODE = {}
for scan, ch in PLAIN.items():
    TO_CODE.setdefault(ch, (scan, False))
for scan, ch in SHIFTED.items():
    TO_CODE.setdefault(ch, (scan, True))
for scan, name in NAMED.items():
    TO_CODE.setdefault(name, (scan, False))
TO_CODE["space"] = ("KEY_SPACE", False)
for ch in "abcdefghijklmnopqrstuvwxyz":
    TO_CODE[ch.upper()] = (f"KEY_{ch.upper()}", True)


def key_name(scan: str, shift: bool) -> str | None:
    """Protocol name for a scan code, given the shift state."""
    if scan in NAMED:
        return NAMED[scan]
    if shift and scan in SHIFTED:
        return SHIFTED[scan]
    if scan in PLAIN:
        return PLAIN[scan].upper() if shift else PLAIN[scan]
    return None


def pick_device(pattern: str | None) -> InputDevice:
    devices = [InputDevice(path) for path in list_devices()]
    candidates = []
    for dev in devices:
        caps = dev.capabilities().get(ecodes.EV_KEY, [])
        looks_like_keyboard = ecodes.KEY_A in caps and ecodes.KEY_Z in caps
        if pattern:
            if re.search(pattern, dev.name, re.I) or pattern == dev.path:
                candidates.append(dev)
        elif looks_like_keyboard:
            candidates.append(dev)
    if not candidates:
        sys.exit("no keyboard found; list devices with --list")
    return candidates[0]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--binary", default="./.lake/build/bin/capslockmode",
                    help="path to the capslockmode executable")
    ap.add_argument("--device", help="device path, or a regex matched against device names")
    ap.add_argument("--list", action="store_true", help="list input devices and exit")
    ap.add_argument("--dry-run", action="store_true",
                    help="print the injected events instead of injecting them")
    ap.add_argument("--no-grab", action="store_true",
                    help="do not take the device exclusively (for debugging)")
    ap.add_argument("--led", action="store_true",
                    help="light the Caps Lock LED while in normal mode")
    ap.add_argument("extra", nargs="*", help="extra arguments passed to `capslockmode run`")
    args = ap.parse_args()

    if args.list:
        for path in list_devices():
            dev = InputDevice(path)
            print(f"{dev.path:20} {dev.name}")
        return 0

    dev = pick_device(args.device)
    print(f"# keyboard: {dev.name} ({dev.path})", file=sys.stderr)

    machine = subprocess.Popen(
        [args.binary, "run", "--verbose", *args.extra],
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        text=True, bufsize=1,
    )

    ui = None if args.dry_run else UInput(name="capslockmode")

    def inject(line: str) -> None:
        """Replay one output event on the virtual keyboard."""
        parts = line.split()
        if len(parts) != 2:
            return
        direction, name = parts
        entry = TO_CODE.get(name)
        if entry is None:
            print(f"# cannot inject {name}", file=sys.stderr)
            return
        scan, needs_shift = entry
        code = ecodes.ecodes[scan]
        value = 1 if direction == "down" else 0
        if args.dry_run:
            print(f"inject {direction} {name}")
            return
        if needs_shift and value == 1:
            ui.write(ecodes.EV_KEY, ecodes.KEY_LEFTSHIFT, 1)
        ui.write(ecodes.EV_KEY, code, value)
        if needs_shift and value == 0:
            ui.write(ecodes.EV_KEY, ecodes.KEY_LEFTSHIFT, 0)
        ui.syn()

    def pump_stdout() -> None:
        for line in machine.stdout:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            inject(line)

    def pump_stderr() -> None:
        for line in machine.stderr:
            line = line.strip()
            print(line, file=sys.stderr)
            if args.led and line.startswith("# mode:") and not args.dry_run:
                normal = "insert" not in line
                try:
                    dev.set_led(ecodes.LED_CAPSL, int(normal))
                except OSError:
                    pass

    threading.Thread(target=pump_stdout, daemon=True).start()
    threading.Thread(target=pump_stderr, daemon=True).start()

    if not args.no_grab:
        dev.grab()
    mods = {"shift": False, "ctrl": False, "alt": False, "super": False}

    try:
        for event in dev.read_loop():
            if event.type != ecodes.EV_KEY:
                continue
            scan = ecodes.KEY[event.code]
            if isinstance(scan, list):
                scan = scan[0]
            name = key_name(scan, mods["shift"])
            if name is None:
                continue
            if name in MODIFIER_KEYS:
                if event.value in (0, 1):
                    mods[name] = bool(event.value)
            if event.value == 2:      # auto-repeat
                direction = "down"
            elif event.value == 1:
                direction = "down"
            elif event.value == 0:
                direction = "up"
            else:
                continue
            held = ",".join(m for m, on in mods.items() if on)
            machine.stdin.write(f"{direction} {name}{(' ' + held) if held else ''}\n")
            machine.stdin.flush()
    except KeyboardInterrupt:
        pass
    finally:
        if not args.no_grab:
            try:
                dev.ungrab()
            except OSError:
                pass
        machine.terminate()
        if ui is not None:
            ui.close()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
