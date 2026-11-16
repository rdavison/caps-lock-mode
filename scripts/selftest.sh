#!/usr/bin/env bash
# End-to-end check of the `capslockmode run` filter: feed it protocol lines on
# stdin, compare what comes back with what we expect.  This exercises the real
# binary, pipes and all, which the in-Lean tests do not.
set -euo pipefail
cd "$(dirname "$0")/.."
BIN=${BIN:-./.lake/build/bin/capslockmode}
[ -x "$BIN" ] || { echo "build first: lake build"; exit 1; }

fail=0
check() {
  local name=$1 input=$2 expected=$3 actual
  actual=$(printf '%s\n' "$input" | "$BIN" run | tr '\n' ' ' | sed 's/ *$//')
  if [ "$actual" = "$expected" ]; then
    printf '  ok   %s\n' "$name"
  else
    printf '  FAIL %s\n       expected: %s\n       actual:   %s\n' "$name" "$expected" "$actual"
    fail=1
  fi
}

echo "capslockmode selftest"

# Insert mode passes everything through, byte for byte.
check "passthrough" \
  $'down h\nup h\ndown i\nup i' \
  "down h up h down i up i"

# Caps Lock is swallowed and switches modes; `h` then means Left.
check "caps then motion" \
  $'down caps\nup caps\ndown h\nup h' \
  "down left up left"

# `dd` compiles to Home, Shift+Down, Delete - and releases Shift again.
check "dd" \
  $'down caps\ndown d\nup d\ndown d\nup d' \
  "down home up home down shift down down up down up shift down del up del"

# A count multiplies the motion, not the operator's own keystrokes.
check "3j" \
  $'down caps\ndown 3\nup 3\ndown j\nup j' \
  "down down up down down down up down down down up down"

# Esc gets you back to normal mode from anywhere, silently.
check "esc is silent" \
  $'down caps\ndown 9\ndown d\ndown esc\nup esc' \
  ""

# Unbound Ctrl chords still reach the application, so Ctrl+S keeps saving.
check "ctrl passthrough" \
  $'down caps\ndown s ctrl' \
  "down ctrl down s up s up ctrl"

if [ "$fail" = 0 ]; then echo "all good"; else echo "failures"; fi
exit $fail
