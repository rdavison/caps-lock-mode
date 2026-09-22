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
  # the same guarantees one level down, where they hold for any backend and not
  # just for vi
  prelude_no_feedback prelude_up_only_if_pressed prelude_toggle_down
  prelude_toggle_up prelude_capsLock_silent
  Quartz.encode_chord Quartz.encode_length Quartz.flags_settle Quartz.chordsOf_encode
  Quartz.decode_key
  Hid.reports_settle Hid.reportAfter_chord Hid.encodeFrom_length
  Hid.apply_nodup Hid.reportAfter_nodup Hid.decode_self
  Kanata.resolve_transparent Kanata.resolve_identity_any Kanata.resolve_identity
  Kanata.release_undoes_press Kanata.release_restores_holds
  Bridge.code_roundTrip Bridge.toKeyCode_injective
  # the dispatcher: transparency re-derived from the evaluator, and the one
  # obligation a backend-agnostic router genuinely has of its own
  Dispatch.wire_roundTrip Dispatch.dispatch_of_claimed
  Dispatch.up_only_if_through Dispatch.down_through_remembered
  Dispatch.select_first Dispatch.select_second
  Dispatch.viAlone_down Dispatch.modal_bound
  Dispatch.kanata_identity Dispatch.dispatch_identity_transparent
  Dispatch.run_identity_transparent
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
