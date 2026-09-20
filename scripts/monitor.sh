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

if [ -n "$OLD" ] && [ "$OLD" != "$NEW" ]; then
  echo
  echo "!! The driver changed since you last granted Accessibility."
  echo "   macOS keys the grant to the old identity, so any existing entry is"
  echo "   now dead. You must REMOVE the capslockmode-quartz entry and add it"
  echo "   again -- re-ticking the old one does nothing."
  echo
fi

if "$BIN" --check >/dev/null 2>&1; then
  echo "==> Accessibility: granted"
else
  BINPATH="$(cd "$(dirname "$BIN")" && pwd)/$(basename "$BIN")"
  echo "==> Accessibility: NOT granted"
  echo "    Add (or remove and re-add) this exact path:"
  echo "      $BINPATH"
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
