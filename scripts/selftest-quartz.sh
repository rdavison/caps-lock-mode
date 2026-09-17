#!/usr/bin/env bash
# End-to-end check of the macOS wire: virtual keycodes and flag masks in,
# the same out.  Run against the real binary, pipes and all.
set -euo pipefail
cd "$(dirname "$0")/.."
BIN=${BIN:-./.lake/build/bin/capslockmode}
[ -x "$BIN" ] || { echo "build first: lake build"; exit 1; }

fail=0
check() {
  local name=$1 input=$2 expected=$3 actual
  actual=$(printf '%s\n' "$input" | "$BIN" run --wire quartz --platform mac \
    | tr '\n' ';' | sed 's/;$//')
  if [ "$actual" = "$expected" ]; then
    printf '  ok   %s\n' "$name"
  else
    printf '  FAIL %s\n       expected: %s\n       actual:   %s\n' "$name" "$expected" "$actual"
    fail=1
  fi
}

echo "capslockmode quartz selftest (keycodes are kVK_* from Carbon Events.h)"

# Caps Lock (57) switches modes and types nothing.
check "caps is silent" $'down 57\nup 57' ""

# `dd` on a Mac is Cmd+Left, Shift+Down, Delete - not Home, Shift+Down, Delete.
check "dd is Cmd-based" \
  $'down 57\ndown 2\nup 2\ndown 2\nup 2' \
  "key down 123 command;key up 123 command;key down 125 shift;key up 125 shift;key down 117 -;key up 117 -"

# Every chord costs exactly two events: the modifiers ride along as flags.
check "w is one event pair" \
  $'down 57\ndown 13\nup 13' \
  "key down 124 alt;key up 124 alt"

# Insert mode keeps a modifier held across a flagsChanged, so Cmd+S still saves.
check "cmd+s survives" \
  $'flags command\ndown 1 command\nup 1 command' \
  "key down 1 command;key up 1 command"

# An event the tap recognises as ours is passed straight back, never re-read.
check "no feedback loop" \
  $'down 57\ndown 2 - injected' \
  "key down 2 -"

# A half-typed `d` and then Esc: the command is abandoned, nothing is typed.
check "esc is silent" $'down 57\ndown 2\ndown 53' ""

if [ "$fail" = 0 ]; then echo "all good"; else echo "failures"; fi
exit $fail
