/-
# Tests for the kanata/Quartz bridge

`CapslockMode/Bridge.lean` proves the one general fact -- a position that
crosses comes back as itself -- and that proof says nothing about whether the
numbers are the numbers Carbon uses.  A table with every entry wrong would
satisfy `code_roundTrip` perfectly.

So the guards below are about the *contents*: the handful of keycodes anyone can
check against `<Carbon/HIToolbox/Events.h>` from memory, the whole `defsrc` of
the config actually in use, and -- the part that would otherwise rot silently --
the positions deliberately left without an image.  A `none` that is pinned is a
recorded gap; a `none` that is not is a key that stopped working.
-/
import CapslockMode
import Tests.Fixtures.Kanata

namespace CapslockMode.Tests.Bridge
open CapslockMode CapslockMode.Kanata

/-- The keycode for a name as a config spells it, which is how every guard below
is written: `ofName?` is the table under test's own front door, so a guard that
went through the constructors instead could pass while no config could reach it. -/
private def kc (s : String) : Option Quartz.KeyCode :=
  (Code.ofName? s).bind Code.toKeyCode?

/-! ## Against Carbon

The eight anyone can recall, and the two that are easy to get backwards. -/

#guard kc "a" == some 0
#guard kc "s" == some 1
#guard kc "caps" == some 57
#guard kc "spc" == some 49
#guard kc "ret" == some 36
#guard kc "esc" == some 53
#guard kc "lsft" == some 56
#guard kc "left" == some 123

-- Caps Lock is not restated here; it is `Quartz.capsLockCode`, the constant the
-- decoder already uses, so the two can never disagree.
#guard kc "caps" == some Quartz.capsLockCode

-- `kVK_RightCommand` is 0x36 and `kVK_Command` is 0x37: Command is the one
-- modifier pair macOS numbers right-before-left.
#guard kc "rmet" == some 54
#guard kc "lmet" == some 55

-- ... and every other pair runs the other way, so the asymmetry is visible.
#guard (kc "lsft", kc "rsft") == (some 56, some 60)
#guard (kc "lalt", kc "ralt") == (some 58, some 61)
#guard (kc "lctl", kc "rctl") == (some 59, some 62)

-- `kVK_F20` sits at 0x5A in the middle of the numpad, which is why Keypad8 and
-- Keypad9 are 91 and 92 rather than 90 and 91.
#guard (kc "f20", kc "kp7", kc "kp8", kc "kp9") == (some 90, some 89, some 91, some 92)

-- The two spellings kanata keeps apart and macOS does too: `yen` is Backslash,
-- `¥` is `kVK_JIS_Yen`.
#guard kc "yen" == some 42
#guard kc "¥" == some 93

/-! ## The real config

Every position the fixture's `defsrc` names has a macOS keycode.  Pinning the
rows rather than only the count means a shifted table shows up as a wrong number
instead of as a still-full list. -/

/-- The fixture, parsed at the width its `defsrc` declares.  The fallback is a
row of Caps Lock keys, which *does* have an image -- so the row guards below are
what actually rules out a parse failure, not the coverage guard. -/
private def real : Cfg 72 :=
  (parseAs 72 Fixture.kanataKbd).toOption.getD (Cfg.identity (Vector.replicate 72 .capsLock))

private def srcCodes : List (Option Quartz.KeyCode) :=
  real.src.toList.map Code.toKeyCode?

#guard srcCodes.length == 72
#guard srcCodes.all Option.isSome

-- `esc f1 ... f12`.  The F-row is the least memorable part of the table and the
-- most reordered: F1 is 122 and F12 is 111, descending in neither direction.
#guard srcCodes.take 13 ==
  [53, 122, 120, 99, 118, 96, 97, 98, 100, 101, 109, 103, 111].map some

-- `grv 1 2 3 4 5 6 7 8 9 0 - = bspc`, where 5 and 6 are swapped relative to the
-- legends (23 then 22) -- a genuine Carbon quirk, not a transcription error.
#guard (srcCodes.drop 13).take 14 ==
  [50, 18, 19, 20, 21, 23, 22, 26, 28, 25, 29, 27, 24, 51].map some

-- `tab q w e r t y u i o p [ ] \`
#guard (srcCodes.drop 27).take 14 ==
  [48, 12, 13, 14, 15, 17, 16, 32, 34, 31, 35, 33, 30, 42].map some

-- `caps a s d f g h j k l ; ' ret`, the row with `g` at 5 and `h` at 4.
#guard (srcCodes.drop 41).take 13 ==
  [57, 0, 1, 2, 3, 5, 4, 38, 40, 37, 41, 39, 36].map some

-- `lsft z x c v b n m , . / rsft`, where `b` is 11 because 10 is the ISO key.
#guard (srcCodes.drop 54).take 12 ==
  [56, 6, 7, 8, 9, 11, 45, 46, 43, 47, 44, 60].map some

-- `lctl lalt lmet spc rmet ralt`
#guard srcCodes.drop 66 == [59, 58, 55, 49, 54, 61].map some

/-! ## Coverage, and the gaps

119 of the 180 codes `Code.every` lists have a macOS position.  The count is
pinned so that adding a `Code` without deciding its keycode is a failing build
rather than a silent `none`. -/

#guard Code.every.length == 180
#guard Code.every.countP (fun c => c.toKeyCode?.isSome) == 119
#guard Extra.every.countP (fun e => (Extra.toKeyCode? e).isSome) == 29

-- kanata names F1 through F24; `kVK_F20` is where Events.h stops.
#guard (kc "f20", kc "f21", kc "f24") == (some 90, none, none)

-- `Code.key (.char 'A')` is not a position -- no unshifted US legend is upper
-- case -- and the guard in `toKeyCode?` says so rather than aliasing it onto
-- `a`.  `ofName?` cannot produce it, so this one goes through the constructor.
#guard Code.toKeyCode? (.key (.char 'A')) == none
#guard Code.toKeyCode? (.key (.char 'a')) == some 0

/-- Every position deliberately left without a macOS keycode, by the reason it
has none.  Spelled as names a config would actually contain, so that a table
change which quietly gives one of these an image fails here. -/
private def deliberatelyNone : List String :=
  -- Not a keycode at all: the mouse is a different event type.
  [ "mlft", "mrgt", "mmid", "mbck", "mfwd", "mwu", "mwd", "mwl", "mwr", "mvmt"
  -- An `NSSystemDefined` event instead of a key event.  The fixture's F-row is
  -- written entirely in these, which is the reason `Code.toPhys?` was not good
  -- enough and this module exists.
  , "🔆", "🔅", "blup", "bldn", "▶⏸", "▶▶", "◀◀", "eject", "🎛"
  -- No such position on macOS.
  , "nlck", "slck", "pause", "sys", "wkup", "bck", "fwd", "menu", "nuhs"
  , "lpar", "rpar"
  -- evdev CJK names with no JIS position behind them.
  , "hiragana", "katakana", "henk", "mhnk"
  -- Application-launch keys, and macOS's own function-row actions, which kanata
  -- carries as KEY_249..253.
  , "hmpg", "mdia", "mail", "email", "calc", "plyr", "powr", "zzz"
  , "sls", "dtn", "dnd", "mctl", "lpad"
  -- Ten codes with no meaning anywhere.
  , "nop0", "nop1", "nop2", "nop3", "nop4", "nop5", "nop6", "nop7", "nop8", "nop9" ]

-- Each one is a name the evaluator knows ...
#guard deliberatelyNone.all (fun s => (Code.ofName? s).isSome)
-- ... and none of them has a keycode.
#guard deliberatelyNone.all (fun s => (kc s).isNone)
-- 57 of the 86 `Extra`s, and the list above names all of them.
#guard deliberatelyNone.length == 57

-- The JIS positions are the other side of that decision: Events.h names them,
-- so they are mapped rather than refused for not being on a US keyboard.
#guard (kc "ro", kc "kana", kc "eisu", kc "kp,") == (some 94, some 104, some 102, some 95)

-- `102d` is `kVK_ISO_Section`, the key between left Shift and `Z`.
#guard kc "102d" == some 10

/-! ## The round trip

`Bridge.code_roundTrip` proves this for every `Code`, including the ones no
config can name.  The guard is here for the other direction of trust: it runs
the actual tables rather than the proof's view of them, so a `decide` that
succeeded for the wrong reason would still be caught. -/

#guard Code.every.all fun c =>
  match c.toKeyCode? with
  | some k => Quartz.codeOf? k == some c
  | none => true

/-- The keycodes this module adds to the ones `Quartz.keyOf?` already knows. -/
private def addedCodes : List Quartz.KeyCode :=
  (Code.every.filter fun c => match c with | .key _ => false | _ => true).filterMap
    Code.toKeyCode?

-- `codeOf?` asks `keyOf?` before it looks at anything else, which is sound only
-- because nothing added here is in `keyOf?`'s range.  That is a fact about two
-- tables, so it is checked rather than proved.
#guard addedCodes.length == 38
#guard addedCodes.all fun k => (Quartz.keyOf? k).isNone

-- ... and they are distinct, which the round-trip theorem already implies via
-- `toKeyCode_injective`; this is the concrete form of it.
#guard addedCodes.eraseDups.length == 38

-- A keycode with no kanata position stays that way.  110 is the value a PC
-- keyboard's Menu key reports, which Events.h does not name and this table
-- therefore does not claim.
#guard Quartz.codeOf? 110 == none
#guard Quartz.codeOf? 52 == none

-- The reverse direction on the keys that matter most, spelled as `defsrc` does.
#guard Quartz.codeOf? 57 == Code.ofName? "caps"
#guard Quartz.codeOf? 56 == Code.ofName? "lsft"
#guard Quartz.codeOf? 123 == Code.ofName? "left"
#guard Quartz.codeOf? 0 == Code.ofName? "a"

end CapslockMode.Tests.Bridge
