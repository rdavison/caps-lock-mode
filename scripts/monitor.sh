#!/usr/bin/env bash
# Launch the monitor with its Accessibility permission actually working.
#
# macOS ties the Accessibility grant to the binary's code identity.  This binary
# is ad-hoc signed, so its CDHash changes every time it is rebuilt, and the
# System Settings entry silently stops applying: the app is still listed, still
# ticked, and still not trusted.  That failure is invisible and costs an hour
# the first time you hit it.
#
# So: rebuild only when the source actually changed, tell you plainly when the
# identity moved, and wait for the grant rather than launching into a window
# that cannot see the keyboard.
set -euo pipefail
cd "$(dirname "$0")/.."

BIN=.lake/build/bin/capslockmode-quartz
SRC=drivers/quartz_bridge.swift
STAMP=.lake/build/.quartz-cdhash

cdhash() { codesign -d --verbose=4 "$1" 2>&1 | sed -n 's/^CDHash=//p'; }

echo "==> building the machine"
lake build >/dev/null

# Only relink when the source is newer: an identical binary keeps its grant.
if [ ! -x "$BIN" ] || [ "$SRC" -nt "$BIN" ]; then
  echo "==> compiling the driver (its identity will change)"
  swiftc -O "$SRC" -o "$BIN"
else
  echo "==> driver is up to date, identity unchanged"
fi

NEW="$(cdhash "$BIN")"
OLD="$(cat "$STAMP" 2>/dev/null || true)"
printf '%s' "$NEW" > "$STAMP"

CHANGED=no
if [ -n "$OLD" ] && [ "$OLD" != "$NEW" ]; then CHANGED=yes; fi

# Check the grant before saying anything about it.  A rebuild changes this
# binary's code identity, and the documented expectation is that the grant dies
# with it -- but observation says otherwise: a grant made for one build has
# survived later rebuilds at the same path.  So report what is true now rather
# than what the identity change predicts.
if "$BIN" --check >/dev/null 2>&1; then
  echo "==> Accessibility: granted"
  if [ "$CHANGED" = yes ]; then
    echo "    (identity changed since the grant, and it still holds)"
  fi
else
  BINPATH="$(cd "$(dirname "$BIN")" && pwd)/$(basename "$BIN")"
  echo "==> Accessibility: NOT granted"
  if [ "$CHANGED" = yes ]; then
    echo "    The driver was rebuilt since the last grant, so REMOVE the existing"
    echo "    capslockmode-quartz entry before adding it back -- re-ticking a dead"
    echo "    entry does nothing."
  fi
  echo "    Add this exact path:"
  echo "      $BINPATH"
  echo "    (run this from your own terminal: macOS resolves the grant through"
  echo "     the responsible process, so another tool's subprocess reads as"
  echo "     untrusted even with the same binary)"
  open "x-apple.systempreferences:com.apple.preference.security?Privacy_Accessibility" || true
  echo -n "    waiting for the grant (Ctrl-C to launch anyway)"
  for _ in $(seq 1 120); do
    if "$BIN" --check >/dev/null 2>&1; then echo; echo "==> Accessibility: granted"; break; fi
    echo -n "."
    sleep 1
  done
  echo
fi

echo "==> launching (opens disarmed; nothing is intercepted until you press Start)"
exec "$BIN" --monitor "$@"
