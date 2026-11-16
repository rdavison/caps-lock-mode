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

# The clock rides as a tag, so a stamped line says exactly what an unstamped one
# says until something actually reads a clock.  This is the md5 check written
# out as a case.
check "a stamp changes nothing by itself" \
  $'down 57 - @10\ndown 2 - @20\nup 2 - @30\ndown 2 - @40\nup 2 - @50' \
  "key down 123 command;key up 123 command;key down 125 shift;key up 125 shift;key down 117 -;key up 117 -"

# Two tags, so they commute.
check "stamp then injected" $'down 57\ndown 2 - @5 injected' "key down 2 -"
check "injected then stamp" $'down 57\ndown 2 - injected @5' "key down 2 -"

# A broken clock looks broken rather than reading as time zero.
check "a bad stamp is dropped" $'down 2 - @x' ""

# --------------------------------------------------------------------------
# With a kanata config bound to insert mode.
#
# Nothing else drives the dispatcher from wire text: `Tests/Dispatch.lean`
# works in positions and guards `ofKeyCode?`/`toKeyCode?` only pointwise, so
# the whole chain -- parse, edges, dispatch, evaluate, keycode, line -- is only
# ever exercised here.
#
# A config written for this test and nowhere else.  `Tests/Fixtures/Kanata.lean`
# argues against a checked-in `.kbd`, and that argument is about duplicating the
# *user's* config into a file no `#guard` can read.  This is four lines with
# exactly one copy, in the script that reads it.
KBD="$(mktemp -t capslockmode-selftest)"
trap 'rm -f "$KBD"' EXIT
cat >"$KBD" <<'EOF'
(defsrc a s d f)
(deflayer base b _ (layer-switch nav) (one-shot 500 lsft))
(deflayer nav _ _ _ _)
EOF

checkK() {
  local name=$1 input=$2 expected=$3 actual
  actual=$(printf '%s\n' "$input" | "$BIN" run --wire quartz --platform mac \
    --kanata "$KBD" 2>/dev/null | tr '\n' ';' | sed 's/;$//')
  if [ "$actual" = "$expected" ]; then
    printf '  ok   %s\n' "$name"
  else
    printf '  FAIL %s\n       expected: %s\n       actual:   %s\n' "$name" "$expected" "$actual"
    fail=1
  fi
}

echo "capslockmode quartz selftest, with a config bound to insert mode"

# `a` (keycode 0) is remapped to `b` (keycode 11): the whole chain in one line.
checkK "the evaluator rewrites in insert" $'down 0\nup 0' "key down 11 -;key up 11 -"

# `_` is transparent, so `s` (keycode 1) is still `s`.
checkK "transparent is unchanged" $'down 1\nup 1' "key down 1 -;key up 1 -"

# Normal mode is still vi's: the same string the unbound `dd` case produces.
checkK "vi still owns normal mode" \
  $'down 57\ndown 2\nup 2\ndown 2\nup 2' \
  "key down 123 command;key up 123 command;key down 125 shift;key up 125 shift;key down 117 -;key up 117 -"

# A position `defsrc` never mentions falls through unchanged: the evaluator is
# the floor, not a filter.
checkK "a position outside defsrc falls through" $'down 48\nup 48' "key down 48 -;key up 48 -"

# Our own event, handed straight back rather than re-read.
checkK "no feedback loop, bound" $'down 0 - injected' "key down 0 -"

# A refused form emits nothing on the wire -- and says so on stderr, which the
# next check covers.
checkK "a refused position is silent on the wire" $'down 3' ""

# ... and is audible.  Captured separately because `checkK` drops stderr.
if printf 'down 3\n' | "$BIN" run --wire quartz --platform mac --kanata "$KBD" 2>&1 >/dev/null \
     | grep -q 'refused: one-shot'; then
  printf '  ok   %s\n' "a refused position is audible"
else
  printf '  FAIL %s\n' "a refused position is audible"
  fail=1
fi

# The banner names what it refused, so a dead key is findable.
if "$BIN" run --wire quartz --kanata "$KBD" </dev/null 2>&1 >/dev/null \
     | grep -q '4 positions, 2 layers'; then
  printf '  ok   %s\n' "the banner says what loaded"
else
  printf '  FAIL %s\n' "the banner says what loaded"
  fail=1
fi

# Rejected, not ignored: the raw wire cannot name a position.
if "$BIN" run --wire raw --kanata "$KBD" </dev/null 2>/dev/null; then
  printf '  FAIL %s\n' "--kanata needs --wire quartz"
  fail=1
else
  printf '  ok   %s\n' "--kanata needs --wire quartz"
fi

# A file that is not there is an error, not an empty config.
if "$BIN" run --wire quartz --kanata /nonexistent.kbd </dev/null 2>/dev/null; then
  printf '  FAIL %s\n' "a missing config is an error"
  fail=1
else
  printf '  ok   %s\n' "a missing config is an error"
fi

if [ "$fail" = 0 ]; then echo "all good"; else echo "failures"; fi
exit $fail
