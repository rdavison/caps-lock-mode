/-
# The bridge: a kanata position is a macOS position

`Kanata.Code` and `Quartz.KeyCode` name the same thing from two directions.  A
`Code` is what a `defsrc` line calls a key; a `KeyCode` is the Carbon virtual
keycode a `CGEvent` carries.  **Both are physical positions**, so the mapping
between them is physical-to-physical and loses nothing in principle -- unlike
`Code.toPhys?`, which throws away the side of a modifier and has no image for
`🔊` at all, and unlike anything involving `Key.char`, which in this project
means *the character the layout produced* rather than a position (see the header
of `Kanata/Keys.lean`).

That is the whole reason this module can carry a round-trip theorem where
`toPhys?` cannot.

## Why it is a module of its own

`CapslockMode/Kanata/*` states in its own header that it imports **only**
`CapslockMode.Key`: that is what keeps `Prelude.lean`'s "the Mathlib surface is
visible in nine lines" property true, because nothing under `Kanata/` drags
Mathlib in.  `Backend/Quartz.lean` imports `Machine` and `Balance` and therefore
all of it.  Putting the bridge in `Kanata/` would import Mathlib into the one
directory that is free of it; putting it in `Backend/Quartz.lean` would make the
macOS backend depend on the kanata evaluator, which it has no use for and which
would drag the s-expression reader into every build of the driver's event model.

So: a new top-level module, beside `Protocol.lean` and `Monitor.lean`, which are
also translations between two vocabularies rather than parts of either.  It is
the *only* place that imports both halves, which is also the honest statement of
what it is -- a seam, and the one file to read when the two tables disagree.

If a second bridge arrives (`Code ↔ Hid.Usage` is the one the plan names), this
becomes a directory; one file is not yet worth one.

## Where the numbers come from

Every keycode here is a `kVK_*` constant from `<Carbon/HIToolbox/Events.h>`.
Where `Quartz.keyCode?` already knows a position, **this module calls it rather
than restating the number** -- so the `Code.key` branch adds no keycodes at all,
and the letters, digits, punctuation, navigation block and F-row cannot drift
apart from the backend's own table.  What is genuinely new here is the block
`CapslockMode.Key` has no constructor for: the eight modifier keys, the numpad,
`fn`, the three volume keys, the ISO and JIS positions, and Caps Lock -- which
reuses `Quartz.capsLockCode`.

A `Code` maps to `none` exactly when Events.h names no constant for that
position.  Those `none`s are pinned in `Tests/Bridge.lean` so that a gap is
recorded rather than discovered later as a silent drop; each is commented below
with the reason, because the reasons differ and conflating them is how a
brightness key ends up typing a letter.
-/
import CapslockMode.Kanata.Keys
import CapslockMode.Backend.Quartz

namespace CapslockMode

namespace Kanata

/-- The macOS virtual keycode for a key `CapslockMode.Key` cannot name.

Three quite different reasons produce a `none` here, and they are kept apart:

* **Not a keycode at all.**  The mouse buttons and the wheel arrive as
  `CGEventMouseDown`/`ScrollWheel` carrying a button number -- a different event
  type, on a different field.  kanata calls them `OsCode`s because evdev does;
  macOS never will.
* **A system-defined event instead.**  Brightness, keyboard illumination,
  play/pause, next/previous track, eject and Dashboard arrive as
  `NSSystemDefined` subtype 8 with an `NX_KEYTYPE_*` in the event data, not as
  key events.  Volume and mute are the exception -- Carbon does name those three
  as virtual keycodes, so they are here.
* **The position does not exist on this platform.**  Num Lock, Scroll Lock,
  Pause, Print Screen, the browser and application-launch keys, the evdev-only
  CJK keys and the ten `nop`s are evdev codes with no macOS counterpart.

The JIS positions (`¥`, `ro`, `kana`, `eisu`, `kp,`) *do* have constants and a
JIS keyboard on a Mac really reports them, so they are mapped.  Only the CJK
names with no constant at all -- `hiragana`, `katakana`, `henk`, `mhnk` -- are
refused.  The alternative, refusing the whole block because a US keyboard has no
such keys, would confuse "the layout has no legend for it" with "the platform
has no code for it", which is the distinction this table exists to record. -/
def Extra.toKeyCode? : Extra → Option Quartz.KeyCode
  -- `kVK_Help` is the Insert position: a PC keyboard's Insert reports 114.
  | .insert => some 114
  -- Events.h names no constant for the Menu/Application key.  The value a PC
  -- keyboard reports for it (0x6E) is real but undocumented, and this table
  -- keeps to one source rather than mixing in folklore.
  | .menu => none
  -- macOS has no Num Lock.  The position is Clear, which `clr` already names
  -- below; mapping both onto 71 would make the table non-injective and take the
  -- round-trip theorem with it.
  | .numLock => none
  -- Scroll Lock, Pause and Print Screen doubled as F14/F15/F13 on old Apple
  -- keyboards, which is to say macOS has codes for the *F-keys*, not for these.
  | .scrollLock => none
  | .pause => none
  | .printScreen => none
  | .eject => none
  | .clear => some 71                 -- kVK_ANSI_KeypadClear
  | .wakeUp => none                   -- power management, not an event at all
  | .browserBack => none
  | .browserForward => none
  | .dashboard => none
  -- `kVK_Function` exists, although macOS normally delivers `fn` as a
  -- `flagsChanged` carrying `NX_SECONDARYFNMASK`.  A position is a position.
  | .fn => some 63
  | .mute => some 74                  -- kVK_Mute
  | .volumeUp => some 72              -- kVK_VolumeUp
  | .volumeDown => some 73            -- kVK_VolumeDown
  | .brightnessUp => none
  | .brightnessDown => none
  | .kbdIllumUp => none
  | .kbdIllumDown => none
  | .playPause => none
  | .nextTrack => none
  | .prevTrack => none
  -- The numpad is contiguous except where `kVK_F20` interrupts it at 0x5A,
  -- which is why 8 and 9 are 91 and 92 rather than 90 and 91.
  | .kp0 => some 82
  | .kp1 => some 83
  | .kp2 => some 84
  | .kp3 => some 85
  | .kp4 => some 86
  | .kp5 => some 87
  | .kp6 => some 88
  | .kp7 => some 89
  | .kp8 => some 91
  | .kp9 => some 92
  | .kpEnter => some 76               -- kVK_ANSI_KeypadEnter
  | .kpDivide => some 75
  | .kpMultiply => some 67
  | .kpMinus => some 78
  | .kpPlus => some 69
  | .kpEqual => some 81               -- kVK_ANSI_KeypadEquals
  | .kpDot => some 65                 -- kVK_ANSI_KeypadDecimal
  | .kpComma => some 95               -- kVK_JIS_KeypadComma
  -- evdev's KEY_KPLEFTPAREN/KPRIGHTPAREN.  No keyboard macOS supports has them.
  | .kpLeftParen => none
  | .kpRightParen => none
  -- `kVK_ISO_Section`: the key between left Shift and `Z` on an ISO keyboard,
  -- which is HID usage 0x64 -- exactly kanata's `102d`/`nubs`.
  | .intlBackslash => some 10
  -- Events.h names no constant for the ISO `#` left of Enter, and the only
  -- candidate (42, Backslash) is already `\`'s.  Folding them together would
  -- break injectivity for a position this table cannot honestly distinguish.
  | .nonUSPound => none
  | .intlRo => some 94                -- kVK_JIS_Underscore
  | .yen => some 93                   -- kVK_JIS_Yen
  | .katakanaHiragana => some 104     -- kVK_JIS_Kana, i.e. HID Lang1
  -- evdev keys with no macOS position; a JIS keyboard has 英数 and かな and
  -- nothing else here.
  | .hiragana => none
  | .katakana => none
  | .henkan => none
  | .muhenkan => none
  | .hanja => some 102                -- kVK_JIS_Eisu, i.e. HID Lang2
  | .mouseLeft => none
  | .mouseRight => none
  | .mouseMid => none
  | .mouseBackward => none
  | .mouseForward => none
  | .wheelUp => none
  | .wheelDown => none
  | .wheelLeft => none
  | .wheelRight => none
  | .mouseMovement => none
  | .homepage => none
  | .media => none
  | .mail => none
  | .email => none
  | .calc => none
  | .player => none
  | .power => none
  | .sleep => none
  -- macOS's own function-row actions.  kanata carries them as KEY_249..253,
  -- evdev codes invented for the purpose; macOS delivers them as system-defined
  -- events, so there is no keycode to give back.
  | .spotlight => none
  | .dictation => none
  | .doNotDisturb => none
  | .missionControl => none
  | .launchpad => none
  -- Ten codes with no meaning anywhere, so certainly not a position.
  | .nop0 => none
  | .nop1 => none
  | .nop2 => none
  | .nop3 => none
  | .nop4 => none
  | .nop5 => none
  | .nop6 => none
  | .nop7 => none
  | .nop8 => none
  | .nop9 => none

/-- The macOS virtual keycode for the position a kanata config names.

The `key` branch delegates to `Quartz.keyCode?` rather than repeating it, so
there is one table for the letters, digits, punctuation, navigation block and
F-row and not two.  The guard is what makes that safe: `keyCode?` lower-cases
its argument, so `Code.key (.char 'A')` -- a `Code` that `Code.ofName?` never
produces, because no unshifted US legend is upper case -- would otherwise land
on `a`'s position and come back as `a`.  Refusing it says the true thing: there
is no position whose unshifted legend is `A`.

The same guard rejects `f21`-`f24`, which kanata accepts and macOS stops naming
at `kVK_F20`. -/
def Code.toKeyCode? : Code → Option Quartz.KeyCode
  | .key k =>
    match Quartz.keyCode? k with
    | some code => if Quartz.keyOf? code = some k then some code else none
    | none => none
  -- Left and right are distinct positions here, which is the thing
  -- `Code.toPhys?` has to throw away and this bridge does not.  Note that
  -- Command is the one pair macOS numbers backwards: right is 54, left is 55.
  | .modifier .shift .left => some 56
  | .modifier .shift .right => some 60
  | .modifier .ctrl .left => some 59
  | .modifier .ctrl .right => some 62
  | .modifier .alt .left => some 58
  | .modifier .alt .right => some 61
  | .modifier .super .left => some 55
  | .modifier .super .right => some 54
  | .capsLock => some Quartz.capsLockCode
  | .extra e => Extra.toKeyCode? e

end Kanata

namespace Quartz

/-- The reverse of `Kanata.Extra.toKeyCode?`, in ascending keycode order so the
two tables can be read against each other in one pass. -/
def extraOf? (c : KeyCode) : Option Kanata.Extra :=
  if c == 10 then some .intlBackslash
  else if c == 63 then some .fn
  else if c == 65 then some .kpDot
  else if c == 67 then some .kpMultiply
  else if c == 69 then some .kpPlus
  else if c == 71 then some .clear
  else if c == 72 then some .volumeUp
  else if c == 73 then some .volumeDown
  else if c == 74 then some .mute
  else if c == 75 then some .kpDivide
  else if c == 76 then some .kpEnter
  else if c == 78 then some .kpMinus
  else if c == 81 then some .kpEqual
  else if c == 82 then some .kp0
  else if c == 83 then some .kp1
  else if c == 84 then some .kp2
  else if c == 85 then some .kp3
  else if c == 86 then some .kp4
  else if c == 87 then some .kp5
  else if c == 88 then some .kp6
  else if c == 89 then some .kp7
  else if c == 91 then some .kp8
  else if c == 92 then some .kp9
  else if c == 93 then some .yen
  else if c == 94 then some .intlRo
  else if c == 95 then some .kpComma
  else if c == 102 then some .hanja
  else if c == 104 then some .katakanaHiragana
  else if c == 114 then some .insert
  else none

/-- The kanata position a virtual keycode names.

`keyOf?` is consulted **first**, and that ordering is load bearing rather than
stylistic: it is what makes the `Code.key` half of `code_roundTrip` a two-line
argument instead of a case analysis over 65536 `UInt16`s.  It is sound because
no keycode this module adds is in `keyOf?`'s range -- `Tests/Bridge.lean` pins
that, since it is a fact about two tables and not something to induct over. -/
def codeOf? (c : KeyCode) : Option Kanata.Code :=
  match keyOf? c with
  | some k => some (.key k)
  | none =>
    if c == capsLockCode then some .capsLock
    else if c == 56 then some (.modifier .shift .left)
    else if c == 60 then some (.modifier .shift .right)
    else if c == 59 then some (.modifier .ctrl .left)
    else if c == 62 then some (.modifier .ctrl .right)
    else if c == 58 then some (.modifier .alt .left)
    else if c == 61 then some (.modifier .alt .right)
    else if c == 55 then some (.modifier .super .left)
    else if c == 54 then some (.modifier .super .right)
    else (extraOf? c).map Kanata.Code.extra

end Quartz

namespace Bridge

open Kanata

/-! ## The round trip

`Code` is not a finite type -- `Code.key (.char c)` ranges over every `Char` and
`Code.key (.f n)` over every `Nat` -- so the proof cannot be one `decide`.  It
splits where the type does: the unbounded `key` branch is proved structurally
from the guard in `toKeyCode?`, and the three finite branches (86 `Extra`s, 8
modifiers, Caps Lock) are decided one constructor at a time, exactly as
`Extra.mem_every` is. -/

/-- One code's round trip as a closed `Bool`, which is the form `decide` can
check.  Stating it as `∀ k, toKeyCode? c = some k → ...` instead would leave a
quantifier over `UInt16` in every case and put 65536 branches in front of the
kernel. -/
private def roundTrips (c : Code) : Bool :=
  match c.toKeyCode? with
  | some k => decide (Quartz.codeOf? k = some c)
  | none => true

private theorem of_roundTrips {c : Code} (h : roundTrips c = true) {k : Quartz.KeyCode}
    (hk : c.toKeyCode? = some k) : Quartz.codeOf? k = some c := by
  unfold roundTrips at h
  rw [hk] at h
  exact of_decide_eq_true h

private theorem extra_roundTrips (e : Extra) : roundTrips (.extra e) = true := by
  cases e <;> decide

private theorem modifier_roundTrips (m : Modifier) (s : Side) :
    roundTrips (.modifier m s) = true := by
  cases m <;> cases s <;> decide

private theorem capsLock_roundTrips : roundTrips .capsLock = true := by decide

/-- The unbounded branch.  Nothing is enumerated: `toKeyCode?` only answers for
a `Key` when `keyOf?` already answers back, and `codeOf?` asks `keyOf?` before
anything else, so the two halves meet on that one hypothesis. -/
theorem key_roundTrip (k : Key) (code : Quartz.KeyCode)
    (h : Code.toKeyCode? (.key k) = some code) : Quartz.codeOf? code = some (.key k) := by
  rw [Code.toKeyCode?] at h
  split at h
  · split at h
    · rename_i hb
      obtain rfl := Option.some.inj h
      simp [Quartz.codeOf?, hb]
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **A position survives the crossing.**  Whenever a kanata `Code` has a macOS
keycode, that keycode names the same `Code` back again.

This is the claim `Code.toPhys?` cannot make -- there the side of a modifier is
gone and every `Extra` is `none` -- and it is what a dispatcher needs in order
to hand an event to the kanata evaluator and to the vi machine and know it gave
them the same key. -/
theorem code_roundTrip (c : Code) (k : Quartz.KeyCode) (h : c.toKeyCode? = some k) :
    Quartz.codeOf? k = some c := by
  cases c with
  | key k' => exact key_roundTrip k' k h
  | modifier m s => exact of_roundTrips (modifier_roundTrips m s) h
  | capsLock => exact of_roundTrips capsLock_roundTrips h
  | extra e => exact of_roundTrips (extra_roundTrips e) h

/-- ... and therefore no two positions share a keycode.  Injectivity is the
operational reading of "not lossy", and it falls straight out of the round trip
rather than needing the 119-way collision check a table this size would
otherwise deserve. -/
theorem toKeyCode_injective {c₁ c₂ : Code} {k : Quartz.KeyCode}
    (h₁ : c₁.toKeyCode? = some k) (h₂ : c₂.toKeyCode? = some k) : c₁ = c₂ :=
  Option.some.inj ((code_roundTrip c₁ k h₁).symm.trans (code_roundTrip c₂ k h₂))

end Bridge

end CapslockMode
