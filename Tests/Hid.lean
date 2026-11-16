/-
# HID backend tests

`Tests/Quartz.lean` checks that every chord the key map plays can be *named* to
macOS.  The obligation here is different, and it is the one a level-based
protocol creates: every chord must be expressible as a sequence of **snapshots**
that returns to empty.

The theorems in `CapslockMode.Backend.Hid` cover the general case.  These guards
cover the part a proof cannot: that the actual key map only uses keys the usage
table knows, so nothing the machine plays silently vanishes on the way out.
-/
import CapslockMode

namespace CapslockMode.Tests.Hid
open CapslockMode CapslockMode.Hid

private def N : Config := { startMode := .normal }

/-- The reports a script produces. -/
private def reportsOf (script : String) (cfg : Config := N) : List Report :=
  encode (run cfg cfg.start (parseScript script)).2

/-- The report a script leaves behind. -/
private def finalReport (script : String) (cfg : Config := N) : Report :=
  reportAfter {} (run cfg cfg.start (parseScript script)).2

/-! ## Usages

The table has to cover what the key map actually plays, on both platforms. -/

#guard usageOf? (.char 'a') == some 0x04
#guard usageOf? (.char 'z') == some 0x1D
#guard usageOf? .left == some 0x50
#guard usageOf? .right == some 0x4F
#guard usageOf? .delete == some 0x4C
#guard usageOf? .home == some 0x4A
#guard usageOf? (.f 1) == some 0x3A
#guard usageOf? (.f 12) == some 0x45
#guard usageOf? (.f 13) == some 0x68
#guard usageOf? (.f 24) == some 0x73
#guard usageOf? (.f 25) == none

-- Caps Lock is an ordinary usage here.  On the Quartz backend it cannot be
-- swallowed at all, which is the whole reason that backend needs a hidutil
-- remap; a seized HID device has no such problem.
#guard physOf? capsLockUsage == some .capsLock
#guard physOf? 0x04 == some (.key (.char 'a'))
#guard physOf? 0x50 == some (.key .left)

/-! ## Every chord the key map plays is expressible

A usage the table does not know would be dropped by `apply`, so the machine
would emit a keystroke that never reaches the wire.  This is the check that
caught the missing F13-F16 entries on the Quartz side. -/

private def emittedKeys (script : String) (cfg : Config := N) : List Key :=
  (run cfg cfg.start (parseScript script)).2.filterMap fun e =>
    match e.key with
    | .key k => some k
    | _ => none

private def allNamed (script : String) (cfg : Config := N) : Bool :=
  (emittedKeys script cfg).all fun k => (usageOf? k).isSome

#guard allNamed "dd"
#guard allNamed "3dd"
#guard allNamed "diw"
#guard allNamed "cw"
#guard allNamed "yy"
#guard allNamed "p"
#guard allNamed "gg"
#guard allNamed "G"
#guard allNamed ">>"
#guard allNamed "x"
#guard allNamed "J"
#guard allNamed "u"

-- and on macOS, where the same commands compile to Cmd-based chords
#guard allNamed "dd" { N with platform := .mac }
#guard allNamed "yy" { N with platform := .mac }
#guard allNamed "gg" { N with platform := .mac }
#guard allNamed "u" { N with platform := .mac }

/-! ## Reports settle

`reports_settle` proves this for any chord sequence.  These check it against the
real key map, the way `Tests/Basic.lean`'s `balancedB` checks `step_balanced` --
if the runtime answer ever disagrees with the theorem, one of them is wrong. -/

#guard finalReport "dd" == {}
#guard finalReport "3dd" == {}
#guard finalReport "ciw" == {}
#guard finalReport "yy" { N with platform := .mac } == {}

/-! ## One report per transition

The level-based counterpart of `Quartz.encode_length`: Quartz hides modifiers in
a mask and gets two events per chord, while here every press and release is its
own snapshot. `dd` on a PC is `home shift+down del`, so the shift adds two
transitions the Quartz stream never spends. -/

#guard (reportsOf "dd").length == (run N N.start (parseScript "dd")).2.length

-- A bare motion holds nothing at the end and touches one key.
#guard finalReport "j" == {}
#guard (reportsOf "j").length == 2

/-! ## Decoding

Diffing a report against itself is silent -- a driver that re-sends state must
not inject phantom keys.  `decode_self` proves it; this pins the direction of a
real transition. -/

#guard decode {} { keys := [0x04] } false
          == [{ dir := .down, key := .key (.char 'a'), mods := {}, injected := false }]

#guard decode { keys := [0x04] } {} false
          == [{ dir := .up, key := .key (.char 'a'), mods := {}, injected := false }]

-- Modifiers come out as their own events, because the machine is edge-based
-- even though the wire is not.
#guard (decode {} { mods := { shift := true } } false).length == 1

end CapslockMode.Tests.Hid
