/-
# kanata's key namespace

`CapslockMode.Key` cannot be reused here and must not be changed.  It has no
modifier keys at all -- that omission is exactly what lets `CapslockMode.Balance`
prove a chord never names the same physical key twice -- and a kanata config
says `lsft` on the first line of every layer.  It also has no Caps Lock and no
`🔊`.  So the evaluator gets its own key type and a one-way bridge back.

It is called `Code`, not `Key`, because inside `CapslockMode.Kanata` a second
`Key` would make every unqualified `Key` in this directory ambiguous.

**The two projects mean different things by a key, and this is the only place
that says so.**  `CapslockMode.Key.char 'q'` means *the character the layout
produced* -- `Protocol.lean` gets it from a driver that has already applied
Shift and the keymap.  `Code.key (.char 'q')` means *the physical position whose
unshifted US legend is `q`*, because that is what `defsrc` names.  Same
constructor, different reading; anyone wiring these two together has to pick one
and convert.

`toPhys?` is the seam, and it is lossy on purpose.  Left and right collapse,
because `PhysKey.mod` cannot tell them apart, and the media keys return `none`.
That `none` is the honest statement of what a later `Machine` integration has to
solve, rather than a silent substitution that would make `🔊` type a letter.

Coverage is the fixture, the alphanumerics, the punctuation row, `f1`-`f24`, the
arrows and navigation block, and the media/brightness set.  Deliberately not the
whole of kanata's `OsCode`: no numpad, no mouse buttons, no CJK input keys, and
no `defcustomkeys`/`deflocalkeys` remapping.  Those are unknown atoms and so
hard parse errors, which is the right answer for a config that uses them.
-/
import CapslockMode.Key

namespace CapslockMode.Kanata

/-- Which of a pair of modifier keys.  kanata distinguishes them; `PhysKey` does
not, which is what `Code.toPhys?` loses. -/
inductive Side where
  | left | right
  deriving DecidableEq, Repr, Inhabited

/-- A key `CapslockMode.Key` has no constructor for.  Split out rather than
added to `Key` because `Key.lean` is off limits to this phase, and because none
of these can appear in a `Chord` anyway. -/
inductive Extra where
  | insert | menu | numLock | scrollLock | pause | printScreen | eject
  | mute | volumeUp | volumeDown
  | brightnessUp | brightnessDown | kbdIllumUp | kbdIllumDown
  | playPause | nextTrack | prevTrack
  deriving DecidableEq, Repr, Inhabited

/-- A physical key as a kanata config names it. -/
inductive Code where
  -- The payload is the *unshifted US legend of the position*, not the character
  -- produced.  See the module header.
  | key (k : Key)
  | modifier (m : Modifier) (side : Side)
  | capsLock
  | extra (e : Extra)
  deriving DecidableEq, Repr, Inhabited

namespace Extra

/-- The canonical short name, in kanata's own spelling. -/
def name : Extra → String
  | .insert => "ins"
  | .menu => "menu"
  | .numLock => "nlck"
  | .scrollLock => "slck"
  | .pause => "pause"
  | .printScreen => "sys"
  | .eject => "eject"
  | .mute => "mute"
  | .volumeUp => "volu"
  | .volumeDown => "vold"
  | .brightnessUp => "brup"
  | .brightnessDown => "brdn"
  | .kbdIllumUp => "blup"
  | .kbdIllumDown => "bldn"
  | .playPause => "pp"
  | .nextTrack => "next"
  | .prevTrack => "prev"

/-- Every spelling kanata accepts for these, including the emoji the fixture's
F-row is written in. -/
def ofName? : String → Option Extra
  | "ins" | "insert" | "Insert" => some .insert
  | "menu" | "apps" | "comp" | "cmp" | "cmps" | "ContextMenu" => some .menu
  | "nlck" | "nlk" | "NumLock" => some .numLock
  | "slck" | "scrlck" | "ScrollLock" => some .scrollLock
  | "pause" | "break" | "brk" | "Pause" => some .pause
  | "sys" | "ssrq" => some .printScreen
  | "eject" | "EjectCD" => some .eject
  | "mute" | "VolumeMute" | "🔇" => some .mute
  | "volu" | "VolumeUp" | "🔊" => some .volumeUp
  | "vold" | "voldwn" | "VolumeDown" | "🔉" => some .volumeDown
  | "brup" | "bru" | "🔆" => some .brightnessUp
  | "brdn" | "brdwn" | "brdown" | "🔅" => some .brightnessDown
  | "blup" => some .kbdIllumUp
  | "bldn" => some .kbdIllumDown
  | "pp" | "MediaPlayPause" | "▶⏸" => some .playPause
  | "next" | "MediaTrackNext" | "▶▶" => some .nextTrack
  | "prev" | "MediaTrackPrevious" | "◀◀" => some .prevTrack
  | _ => none

end Extra

namespace Code

/-- The canonical short name.  Written in the idiom of `Protocol.Key.name`: one
name out, many names in. -/
def name : Code → String
  | .key k =>
    match k with
    -- The backtick is the one punctuation key whose canonical kanata name is
    -- not the character itself.
    | .char c => if c == '`' then "grv" else String.singleton c
    | .esc => "esc"
    | .tab => "tab"
    | .enter => "ret"
    | .backspace => "bspc"
    | .delete => "del"
    | .space => "spc"
    | .left => "left"
    | .right => "rght"
    | .up => "up"
    | .down => "down"
    | .home => "home"
    | .«end» => "end"
    | .pageUp => "pgup"
    | .pageDown => "pgdn"
    | .f n => s!"f{n}"
  | .modifier .shift .left => "lsft"
  | .modifier .shift .right => "rsft"
  | .modifier .ctrl .left => "lctl"
  | .modifier .ctrl .right => "rctl"
  | .modifier .alt .left => "lalt"
  | .modifier .alt .right => "ralt"
  | .modifier .super .left => "lmet"
  | .modifier .super .right => "rmet"
  | .capsLock => "caps"
  | .extra e => e.name

private def digits? (cs : List Char) : Option Nat :=
  if cs.isEmpty || !cs.all Char.isDigit then none else some (String.ofList cs).toNat!

/-- `F1`-`F24`, either case.  Stopping at 24 is kanata's own limit, not an
arbitrary one: there is no `OsCode` past `KEY_F24`. -/
private def fkey? (cs : List Char) : Option Code :=
  match digits? cs with
  | some n => if 1 ≤ n && n ≤ 24 then some (.key (.f n)) else none
  | none => none

/-- Every spelling this evaluator accepts.

Many-to-one, which is the point: kanata takes both its own short names and the
W3C `event.code` names, and a config mixes them freely.  The prefix rules at the
bottom (`Key`+letter, `Digit`+digit, `F`/`f`+number) keep 60-odd alphanumeric
and function keys out of the table.

Note which spellings are *missing* from kanata's big match and come from
`add_default_str_osc_mappings` instead -- `, . / ; ' [ ] \ - =` and the backtick.
They are folded in here rather than kept in a second table, because the
distinction only matters to `defcustomkeys`, which this evaluator rejects. -/
def ofName? (s : String) : Option Code :=
  match s with
  | "grv" | "grave" | "`" | "Backquote" => some (.key (.char '`'))
  | "min" | "minus" | "-" | "Minus" => some (.key (.char '-'))
  | "eql" | "=" | "Equal" => some (.key (.char '='))
  | "lbrc" | "[" | "BracketLeft" => some (.key (.char '['))
  | "rbrc" | "]" | "BracketRight" => some (.key (.char ']'))
  | "bksl" | "\\" | "Backslash" => some (.key (.char '\\'))
  | "scln" | ";" | "Semicolon" => some (.key (.char ';'))
  | "apo" | "apos" | "'" | "Quote" => some (.key (.char '\''))
  | "comm" | "," | "Comma" => some (.key (.char ','))
  | "." | "Period" => some (.key (.char '.'))
  | "/" | "Slash" => some (.key (.char '/'))
  | "esc" | "escape" | "Escape" => some (.key .esc)
  | "tab" | "Tab" => some (.key .tab)
  | "ret" | "return" | "ent" | "enter" | "Enter" => some (.key .enter)
  | "bspc" | "bks" | "backspace" | "Backspace" => some (.key .backspace)
  | "del" | "delete" | "Delete" => some (.key .delete)
  | "spc" | "space" | "Space" => some (.key .space)
  | "left" | "lft" | "ArrowLeft" => some (.key .left)
  | "rght" | "right" | "ArrowRight" => some (.key .right)
  | "up" | "ArrowUp" => some (.key .up)
  | "down" | "ArrowDown" => some (.key .down)
  | "home" | "Home" => some (.key .home)
  | "end" | "End" => some (.key .«end»)
  | "pgup" | "pageup" | "PageUp" => some (.key .pageUp)
  | "pgdn" | "pagedown" | "PageDown" => some (.key .pageDown)
  | "caps" | "capslock" | "CapsLock" => some .capsLock
  | "lsft" | "lshift" | "lshft" | "shft" | "sft" | "ShiftLeft" =>
      some (.modifier .shift .left)
  | "rsft" | "rshift" | "rshft" | "ShiftRight" | "RightShift" =>
      some (.modifier .shift .right)
  | "lctl" | "lctrl" | "ctl" | "ControlLeft" => some (.modifier .ctrl .left)
  | "rctl" | "rctrl" | "ControlRight" => some (.modifier .ctrl .right)
  | "lalt" | "alt" | "AltLeft" => some (.modifier .alt .left)
  | "ralt" | "altgr" | "AltRight" => some (.modifier .alt .right)
  | "lmet" | "lmeta" | "met" | "MetaLeft" => some (.modifier .super .left)
  | "rmet" | "rmeta" | "MetaRight" => some (.modifier .super .right)
  | _ =>
    match Extra.ofName? s with
    | some e => some (.extra e)
    | none =>
      match s.toList with
      -- Single characters first, so `f` is the letter and not a malformed `f1`.
      | [c] =>
        if (c.isAlpha && c.isLower) || c.isDigit then some (.key (.char c)) else none
      | 'K' :: 'e' :: 'y' :: [c] =>
        if c.isAlpha && c.isUpper then some (.key (.char c.toLower)) else none
      | 'D' :: 'i' :: 'g' :: 'i' :: 't' :: [c] =>
        if c.isDigit then some (.key (.char c)) else none
      | 'f' :: ds => fkey? ds
      | 'F' :: ds => fkey? ds
      | _ => none

/-- Back to the project's own vocabulary.

Lossy, and the losses are the interesting part: the side of a modifier is gone
because `PhysKey.mod` has nowhere to put it, and `extra` has no image at all.
Those are the two things a `Machine` integration will have to answer first. -/
def toPhys? : Code → Option PhysKey
  | .key k => some (.key k)
  | .modifier m _ => some (.mod m)
  | .capsLock => some .capsLock
  | .extra _ => none

/-- Every `Code` this module claims to know, for the round-trip guard in
`Tests/Kanata.lean`.  Drift between `name` and `ofName?` is caught by a test and
not by a proof: the two are independent tables, so there is nothing to induct
over. -/
def every : List Code :=
  (("abcdefghijklmnopqrstuvwxyz0123456789-=[]\\;',./`".toList).map (fun c => .key (.char c))) ++
  [ .key .esc, .key .tab, .key .enter, .key .backspace, .key .delete, .key .space
  , .key .left, .key .right, .key .up, .key .down
  , .key .home, .key .«end», .key .pageUp, .key .pageDown ] ++
  ((List.range 24).map (fun i => .key (.f (i + 1)))) ++
  [ .modifier .shift .left, .modifier .shift .right
  , .modifier .ctrl .left, .modifier .ctrl .right
  , .modifier .alt .left, .modifier .alt .right
  , .modifier .super .left, .modifier .super .right
  , .capsLock ] ++
  [ .insert, .menu, .numLock, .scrollLock, .pause, .printScreen, .eject
  , .mute, .volumeUp, .volumeDown
  , .brightnessUp, .brightnessDown, .kbdIllumUp, .kbdIllumDown
  , .playPause, .nextTrack, .prevTrack ].map Code.extra

end Code

end CapslockMode.Kanata
