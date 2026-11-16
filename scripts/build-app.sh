#!/usr/bin/env bash
# Build the monitor as a real .app bundle, signed so that TCC will hold a grant.
#
# Why a bundle at all.  macOS attributes an Accessibility grant to the
# *responsible process* in the launch chain.  A bare executable started from a
# shell is attributed to the terminal that started it, so adding the binary to
# System Settings does nothing at all -- the entry sits there, ticked and inert,
# and the failure is completely silent.  An .app launched with `open` is its own
# responsible process, so the grant lands on this app, and granting it does not
# hand the same power to everything else you run from a shell.
#
# The grant is pinned to the bundle's code identity, and an ad-hoc signature
# gets a new identity on every rebuild.  So: recompile only when the source
# actually moved, and say plainly when the identity shifted under a live grant.
set -euo pipefail
cd "$(dirname "$0")/.."

APP=".lake/build/CapslockMode.app"
EXE="$APP/Contents/MacOS/capslockmode-quartz"
SRC="drivers/quartz_bridge.swift"
LEAN=".lake/build/bin/capslockmode"
STAMP=".lake/build/.app-cdhash"

cdhash() { codesign -d --verbose=4 "$1" 2>&1 | sed -n 's/^CDHash=//p'; }

echo "==> building the machine"
lake build >/dev/null

if [ ! -x "$EXE" ] || [ "$SRC" -nt "$EXE" ] || [ "$LEAN" -nt "$EXE" ]; then
  echo "==> assembling the bundle (its identity will change)"
  rm -rf "$APP"
  mkdir -p "$APP/Contents/MacOS"
  swiftc -O "$SRC" -o "$EXE"

  # The driver resolves the Lean binary as a sibling of its own executable, so
  # it has to live inside the bundle.  A copy, not a hard link: codesign would
  # follow a link back into .lake and re-sign the build output in place.
  cp "$LEAN" "$APP/Contents/MacOS/capslockmode"

  cat > "$APP/Contents/Info.plist" <<'PLIST'
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
  <key>CFBundleName</key><string>CapslockMode</string>
  <key>CFBundleDisplayName</key><string>CapslockMode monitor</string>
  <key>CFBundleIdentifier</key><string>com.rdavison.capslockmode</string>
  <key>CFBundleExecutable</key><string>capslockmode-quartz</string>
  <key>CFBundlePackageType</key><string>APPL</string>
  <key>CFBundleInfoDictionaryVersion</key><string>6.0</string>
  <key>CFBundleShortVersionString</key><string>0.1.0</string>
  <key>CFBundleVersion</key><string>1</string>
  <key>NSPrincipalClass</key><string>NSApplication</string>
  <key>NSHumanReadableCopyright</key><string>CapslockMode</string>
  <key>LSMinimumSystemVersion</key><string>13.0</string>
</dict>
</plist>
PLIST

  # Nested Mach-O first, then the bundle.  Signing a bundle seals what is nested
  # inside it, and an unsigned nested executable fails that seal.
  codesign -f -s - "$APP/Contents/MacOS/capslockmode" 2>/dev/null
  codesign -f -s - "$APP" 2>/dev/null
else
  echo "==> bundle is up to date, identity unchanged"
fi

codesign -v "$APP" 2>/dev/null && echo "==> signature verifies"

NEW="$(cdhash "$APP")"
OLD="$(cat "$STAMP" 2>/dev/null || true)"
printf '%s' "$NEW" > "$STAMP"
if [ -n "$OLD" ] && [ "$OLD" != "$NEW" ]; then
  echo "==> identity changed since the last build"
  echo "    If CapslockMode was already granted Accessibility, REMOVE the entry"
  echo "    and let the app ask again -- re-ticking a dead entry does nothing."
fi

APPPATH="$(cd "$(dirname "$APP")" && pwd)/$(basename "$APP")"
echo "==> built: $APPPATH"

if [ "${1:-}" = "--open" ]; then
  echo "==> launching (opens disarmed; nothing is intercepted until you press Start)"
  open "$APPPATH"
else
  echo "    launch it with:  open '$APPPATH'"
fi
