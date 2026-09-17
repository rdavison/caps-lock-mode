#!/usr/bin/env bash
# A proof with a `sorry` in it still compiles, so check what the headline
# theorems actually depend on.  Anything beyond Lean's three standard axioms
# (propext, Classical.choice, Quot.sound) is a hole.
set -euo pipefail
cd "$(dirname "$0")/.."

theorems=(
  step_balanced up_only_if_pressed down_remembered run_insert_transparent
  step_insert capsLock_twice SettledMode.toggle_involutive esc_resets
  step_count_le command_repeats_le operator_progress textObj_progress
  Chord.emit_balanced emitChords_balanced Chord.emit_length_le
  no_feedback
  Quartz.encode_chord Quartz.encode_length Quartz.flags_settle Quartz.chordsOf_encode
  Quartz.decode_key
)

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
{
  echo 'import CapslockMode'
  echo 'open CapslockMode'
  for t in "${theorems[@]}"; do echo "#print axioms $t"; done
} > "$tmp/Axioms.lean"

out=$(lake env lean "$tmp/Axioms.lean")
echo "$out"
if echo "$out" | grep -q "sorryAx"; then
  echo "FAIL: a theorem depends on sorry"
  exit 1
fi
echo "all ${#theorems[@]} theorems are sorry-free"
