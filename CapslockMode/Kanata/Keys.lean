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
because `PhysKey.mod` cannot tell them apart, and everything in `Extra` returns
`none`.  That `none` is the honest statement of what a later `Machine`
integration has to solve, rather than a silent substitution that would make `🔊`
type a letter.

## The table is kanata's, at one stated platform

Every name below comes from `parser/src/keys/mod.rs` -- `str_to_oscode` and the
`add_default_str_osc_mappings` fallbacks, which are folded together here because
the distinction between them only matters to `defcustomkeys`, which this
evaluator rejects.

kanata's match is `#[cfg]`-gated in nine places, and the gates disagree: `kana`
is `KEY_HANGEUL` on macOS and Windows but `KEY_KATAKANAHIRAGANA` on Linux, and
`PrintScreen` is `KEY_SYSRQ` everywhere but Windows.  A platform-free evaluator
has to pick one, and the one it picks is **kanata's own `target_os = "unknown"`
build** -- the configuration with no platform, which is the only principled
choice available and which happens to enable every gated arm except the two
Windows ones and `Lang1`.  Anything that reads differently on a real macOS
kanata is called out at the line it affects.

What is deliberately still out: `defcustomkeys` / `deflocalkeys-*` remapping,
which would make this table mutable and is a whole top-level form rather than a
gap in one.  An atom with no entry here is a hard parse error, which is the
right answer for a config that needs a table this one does not have.
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
of these can appear in a `Chord` anyway.

Every constructor is nullary, and that is load-bearing rather than incidental:
Lean's `DecidableEq` deriving has a special path for enum inductives that
compares constructor indices, so an 86-way flat enum costs what a two-way one
does.  Grouping the numpad or the mouse into a nested inductive would give the
payload path and 400-odd generated cases instead. -/
inductive Extra where
  -- The editing and system block.
  | insert | menu | numLock | scrollLock | pause | printScreen | eject | clear
  | wakeUp | browserBack | browserForward | dashboard | fn
  -- Media and brightness.
  | mute | volumeUp | volumeDown
  | brightnessUp | brightnessDown | kbdIllumUp | kbdIllumDown
  | playPause | nextTrack | prevTrack
  -- The numpad, which is a second set of positions and not the digit row.
  | kp0 | kp1 | kp2 | kp3 | kp4 | kp5 | kp6 | kp7 | kp8 | kp9
  | kpEnter | kpDivide | kpMultiply | kpMinus | kpPlus | kpEqual
  | kpDot | kpComma | kpLeftParen | kpRightParen
  -- Positions a US layout does not have.
  | intlBackslash | nonUSPound | intlRo | yen
  -- Japanese input-method keys.
  | katakanaHiragana | hiragana | katakana | henkan | muhenkan | hanja
  -- Mouse.  A `Code` because kanata's `defsrc` takes these as input positions;
  -- in *action* position they are refused, see `Config.worldForms`.
  | mouseLeft | mouseRight | mouseMid | mouseBackward | mouseForward
  | wheelUp | wheelDown | wheelLeft | wheelRight | mouseMovement
  -- Application-launch keys.
  | homepage | media | mail | email | calc | player | power | sleep
  -- macOS's own function row, which kanata carries as KEY_249 through KEY_253.
  | spotlight | dictation | doNotDisturb | missionControl | launchpad
  -- Ten codes with no meaning at all, for naming a position in a sequence.
  | nop0 | nop1 | nop2 | nop3 | nop4 | nop5 | nop6 | nop7 | nop8 | nop9
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

/-- The canonical short name, in kanata's own spelling.

Where kanata offers no short name the long one is canonical: `NumpadEqual` and
`🎛` have nothing else, and `kp=` is *not* free for the first of them because
kanata spends it on `KEY_CLEAR`. -/
def name : Extra → String
  | .insert => "ins"
  | .menu => "menu"
  | .numLock => "nlck"
  | .scrollLock => "slck"
  | .pause => "pause"
  | .printScreen => "sys"
  | .eject => "eject"
  | .clear => "clr"
  | .wakeUp => "wkup"
  | .browserBack => "bck"
  | .browserForward => "fwd"
  | .dashboard => "🎛"
  | .fn => "fn"
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
  | .kp0 => "kp0"
  | .kp1 => "kp1"
  | .kp2 => "kp2"
  | .kp3 => "kp3"
  | .kp4 => "kp4"
  | .kp5 => "kp5"
  | .kp6 => "kp6"
  | .kp7 => "kp7"
  | .kp8 => "kp8"
  | .kp9 => "kp9"
  | .kpEnter => "kprt"
  | .kpDivide => "kp/"
  | .kpMultiply => "kp*"
  | .kpMinus => "kp-"
  | .kpPlus => "kp+"
  | .kpEqual => "NumpadEqual"
  | .kpDot => "kp."
  | .kpComma => "kp,"
  | .kpLeftParen => "lpar"
  | .kpRightParen => "rpar"
  | .intlBackslash => "102d"
  | .nonUSPound => "nuhs"
  | .intlRo => "ro"
  | .yen => "¥"
  | .katakanaHiragana => "kana"
  | .hiragana => "hiragana"
  | .katakana => "katakana"
  | .henkan => "henk"
  | .muhenkan => "mhnk"
  | .hanja => "eisu"
  | .mouseLeft => "mlft"
  | .mouseRight => "mrgt"
  | .mouseMid => "mmid"
  | .mouseBackward => "mbck"
  | .mouseForward => "mfwd"
  | .wheelUp => "mwu"
  | .wheelDown => "mwd"
  | .wheelLeft => "mwl"
  | .wheelRight => "mwr"
  | .mouseMovement => "mvmt"
  | .homepage => "hmpg"
  | .media => "mdia"
  | .mail => "mail"
  | .email => "email"
  | .calc => "calc"
  | .player => "plyr"
  | .power => "powr"
  | .sleep => "zzz"
  | .spotlight => "sls"
  | .dictation => "dtn"
  | .doNotDisturb => "dnd"
  | .missionControl => "mctl"
  | .launchpad => "lpad"
  | .nop0 => "nop0"
  | .nop1 => "nop1"
  | .nop2 => "nop2"
  | .nop3 => "nop3"
  | .nop4 => "nop4"
  | .nop5 => "nop5"
  | .nop6 => "nop6"
  | .nop7 => "nop7"
  | .nop8 => "nop8"
  | .nop9 => "nop9"

/-- The numpad, split out of `ofName?` only to keep each generated string match
to a size that reads in a stack trace.

`kp=` is `KEY_CLEAR` and not `KEY_KPEQUAL`, which looks like a typo in kanata and
is not: `clr` is its other spelling, and the numpad `=` is `NumpadEqual`. -/
def numpadOfName? : String → Option Extra
  | "Numpad0" | "kp0" | "🔢₀" => some .kp0
  | "Numpad1" | "kp1" | "🔢₁" => some .kp1
  | "Numpad2" | "kp2" | "🔢₂" => some .kp2
  | "Numpad3" | "kp3" | "🔢₃" => some .kp3
  | "Numpad4" | "kp4" | "🔢₄" => some .kp4
  | "Numpad5" | "kp5" | "🔢₅" => some .kp5
  | "Numpad6" | "kp6" | "🔢₆" => some .kp6
  | "Numpad7" | "kp7" | "🔢₇" => some .kp7
  | "Numpad8" | "kp8" | "🔢₈" => some .kp8
  | "Numpad9" | "kp9" | "🔢₉" => some .kp9
  | "NumpadEnter" | "kprt" | "🔢⏎" | "🔢↩" | "🔢↵" | "🔢↲" | "🔢⤶" | "🔢⎆" | "🔢⌤" | "🔢␤" =>
      some .kpEnter
  | "NumpadDivide" | "kp/" | "🔢⁄" => some .kpDivide
  | "NumpadMultiply" | "kp*" | "🔢∗" => some .kpMultiply
  | "NumpadSubtract" | "kp-" | "🔢₋" => some .kpMinus
  -- `+` is one of the `add_default_str_osc_mappings` fallbacks, and it is the
  -- numpad plus rather than the shifted `=` of the digit row.
  | "NumpadAdd" | "kp+" | "🔢₊" | "+" => some .kpPlus
  | "NumpadEqual" | "🔢₌" => some .kpEqual
  | "NumpadDecimal" | "kp." | "🔢．" => some .kpDot
  | "NumpadComma" | "kp," | "🔢⸴" => some .kpComma
  | "NumpadLeftParen" | "leftparen" | "lpar" | "kp(" | "🔢₍" => some .kpLeftParen
  | "NumpadRightParen" | "rightparen" | "rpar" | "kp)" | "🔢₎" => some .kpRightParen
  | _ => none

/-- The mouse.  These are `OsCode`s to kanata as much as `a` is, which is why
they are keys here and not actions; `(deflayer x mlft)` is refused a layer up,
in `Config.parseAtom`, exactly as kanata refuses `mvmt` there. -/
def mouseOfName? : String → Option Extra
  | "mlft" | "mouseleft" | "🖰1" | "‹🖰" => some .mouseLeft
  | "mrgt" | "mouseright" | "🖰2" | "🖰›" => some .mouseRight
  | "mmid" | "mousemid" | "🖰3" => some .mouseMid
  | "mbck" | "mousebackward" | "🖰4" => some .mouseBackward
  | "mfwd" | "mouseforward" | "🖰5" => some .mouseForward
  | "mwu" | "mousewheelup" => some .wheelUp
  | "mwd" | "mousewheeldown" => some .wheelDown
  | "mwl" | "mousewheelleft" => some .wheelLeft
  | "mwr" | "mousewheelright" => some .wheelRight
  | "mvmt" | "mousemovement" | "🖰mv" => some .mouseMovement
  | _ => none

/-- Every spelling kanata accepts for these, including the emoji the fixture's
F-row is written in. -/
def ofName? (s : String) : Option Extra :=
  match s with
  | "ins" | "insert" | "Insert" | "⎀" => some .insert
  | "menu" | "apps" | "comp" | "cmp" | "cmps" | "ContextMenu" | "▤" | "☰" | "𝌆" => some .menu
  | "nlck" | "nlk" | "NumLock" | "⇭" => some .numLock
  | "slck" | "scrlck" | "ScrollLock" | "⇳🔒" => some .scrollLock
  | "pause" | "break" | "brk" | "Pause" => some .pause
  -- `PrintScreen` and `sys` are the same `KEY_SYSRQ` everywhere but Windows,
  -- where kanata splits `PrintScreen` off onto `KEY_PRINT`.
  | "sys" | "ssrq" | "PrintScreen" | "prtsc" | "prnt" | "⎙" => some .printScreen
  | "eject" | "EjectCD" => some .eject
  | "clr" | "kp=" => some .clear
  | "wkup" | "WakeUp" => some .wakeUp
  | "bck" | "BrowserBack" => some .browserBack
  | "fwd" | "BrowserForward" => some .browserForward
  | "🎛" => some .dashboard
  | "fn" | "🌐" | "ƒ" | "ⓕ" | "Ⓕ" | "🄵" | "🅕" | "🅵" => some .fn
  | "mute" | "VolumeMute" | "🔇" | "🔈⓪" | "🔈⓿" | "🔈₀" => some .mute
  | "volu" | "VolumeUp" | "🔊" | "🔈+" | "🔈➕" | "🔈₊" | "🔈⊕" => some .volumeUp
  | "vold" | "voldwn" | "VolumeDown" | "🔉" | "🔈−" | "🔈➖" | "🔈₋" | "🔈⊖" => some .volumeDown
  | "brup" | "bru" | "🔆" => some .brightnessUp
  | "brdn" | "brdwn" | "brdown" | "🔅" => some .brightnessDown
  | "blup" | "⌨💡+" | "⌨💡➕" | "⌨💡₊" | "⌨💡⊕" => some .kbdIllumUp
  | "bldn" | "⌨💡−" | "⌨💡➖" | "⌨💡₋" | "⌨💡⊖" => some .kbdIllumDown
  | "pp" | "MediaPlayPause" | "▶⏸" => some .playPause
  | "next" | "MediaTrackNext" | "▶▶" => some .nextTrack
  | "prev" | "MediaTrackPrevious" | "◀◀" => some .prevTrack
  -- The non-US backslash by the left Shift.  kanata spells the short name
  -- `102d`; `102nd` is the evdev name and is *not* accepted.
  | "102d" | "lsgt" | "nubs" | "nonusbslash" | "IntlBackslash" | "﹨" | "<" =>
      some .intlBackslash
  -- The ISO `#` left of Enter.  A distinct HID usage on macOS; Linux evdev folds
  -- it onto Backslash, so on a real Linux kanata this name does not exist.
  | "nuhs" | "non_us_pound" | "NonUSPound" => some .nonUSPound
  | "ro" | "IntlRo" => some .intlRo
  -- Only the Unicode spelling is the yen *key*.  The ASCII `yen` is Backslash,
  -- because in some locales the two share a position, and that is kanata's own
  -- decision rather than an approximation made here.
  | "¥" => some .yen
  -- `kana` reads as `Lang1` on a real macOS kanata.  See the module header.
  | "kana" | "katakanahiragana" => some .katakanaHiragana
  | "hiragana" => some .hiragana
  | "katakana" => some .katakana
  | "henk" | "hnk" | "henkan" | "cnv" | "conv" => some .henkan
  | "mhnk" | "ncnv" | "muhenkan" => some .muhenkan
  | "eisu" | "Lang2" => some .hanja
  | "hmpg" | "homepage" => some .homepage
  | "mdia" | "media" => some .media
  | "mail" | "LaunchMail" => some .mail
  | "email" => some .email
  | "calc" => some .calc
  | "plyr" | "player" => some .player
  | "powr" | "power" => some .power
  | "zzz" | "sleep" => some .sleep
  | "sls" | "SpotLightSearch" => some .spotlight
  | "dtn" | "Dictation" => some .dictation
  | "dnd" | "DoNotDisturb" => some .doNotDisturb
  | "mctl" | "MissionControl" => some .missionControl
  | "lpad" | "LaunchPad" => some .launchpad
  | "nop0" => some .nop0
  | "nop1" => some .nop1
  | "nop2" => some .nop2
  | "nop3" => some .nop3
  | "nop4" => some .nop4
  | "nop5" => some .nop5
  | "nop6" => some .nop6
  | "nop7" => some .nop7
  | "nop8" => some .nop8
  | "nop9" => some .nop9
  | _ =>
    match numpadOfName? s with
    | some e => some e
    | none => mouseOfName? s

/-- Every `Extra`, for the round-trip guard in `Tests/Kanata.lean`. -/
def every : List Extra :=
  [ .insert, .menu, .numLock, .scrollLock, .pause, .printScreen, .eject, .clear
  , .wakeUp, .browserBack, .browserForward, .dashboard, .fn
  , .mute, .volumeUp, .volumeDown
  , .brightnessUp, .brightnessDown, .kbdIllumUp, .kbdIllumDown
  , .playPause, .nextTrack, .prevTrack
  , .kp0, .kp1, .kp2, .kp3, .kp4, .kp5, .kp6, .kp7, .kp8, .kp9
  , .kpEnter, .kpDivide, .kpMultiply, .kpMinus, .kpPlus, .kpEqual
  , .kpDot, .kpComma, .kpLeftParen, .kpRightParen
  , .intlBackslash, .nonUSPound, .intlRo, .yen
  , .katakanaHiragana, .hiragana, .katakana, .henkan, .muhenkan, .hanja
  , .mouseLeft, .mouseRight, .mouseMid, .mouseBackward, .mouseForward
  , .wheelUp, .wheelDown, .wheelLeft, .wheelRight, .mouseMovement
  , .homepage, .media, .mail, .email, .calc, .player, .power, .sleep
  , .spotlight, .dictation, .doNotDisturb, .missionControl, .launchpad
  , .nop0, .nop1, .nop2, .nop3, .nop4, .nop5, .nop6, .nop7, .nop8, .nop9 ]

/-- `every` really is every one.

86 constructors are too many to keep a list in step with by hand, and the
round-trip guard in `Tests/Kanata.lean` only tests the names of codes this list
mentions -- so a constructor left out of it would silently go untested.  That
makes completeness the one fact here worth proving rather than testing, and it
is a `decide` away because `Extra` is finite and flat. -/
theorem mem_every (e : Extra) : e ∈ every := by
  cases e <;> decide

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

Many-to-one, which is the point: kanata takes its own short names, the W3C
`event.code` names *and* a Unicode spelling for most keys, and a config mixes
them freely.  The prefix rules at the bottom (`Key`+letter, `Digit`+digit,
`F`/`f`+number) keep 60-odd alphanumeric and function keys out of the table.

Note which spellings are *missing* from kanata's big match and come from
`add_default_str_osc_mappings` instead -- `, . / ; ' [ ] \ - =`, the backtick,
`{`, `}`, `+` and `yen`.  They are folded in here rather than kept in a second
table, because the distinction only matters to `defcustomkeys`, which this
evaluator rejects. -/
def ofName? (s : String) : Option Code :=
  match s with
  | "grv" | "grave" | "`" | "Backquote" | "ˋ" | "˜" => some (.key (.char '`'))
  | "min" | "minus" | "-" | "Minus" | "‐" => some (.key (.char '-'))
  | "eql" | "=" | "Equal" | "₌" => some (.key (.char '='))
  | "lbrc" | "[" | "{" | "BracketLeft" | "【" | "「" | "〔" | "⎡" => some (.key (.char '['))
  | "rbrc" | "]" | "}" | "BracketRight" | "】" | "」" | "〕" | "⎣" => some (.key (.char ']'))
  -- `yen` is Backslash and `¥` is the yen key; kanata means both.
  | "bksl" | "\\" | "yen" | "Backslash" | "⧵" | "＼" => some (.key (.char '\\'))
  | "scln" | ";" | "Semicolon" | "︔" => some (.key (.char ';'))
  | "apo" | "apos" | "'" | "Quote" => some (.key (.char '\''))
  | "comm" | "," | "Comma" | "⸴" => some (.key (.char ','))
  | "." | "Period" | "．" => some (.key (.char '.'))
  | "/" | "Slash" | "⁄" => some (.key (.char '/'))
  | "esc" | "escape" | "Escape" | "⎋" => some (.key .esc)
  | "tab" | "Tab" | "⭾" | "↹" => some (.key .tab)
  | "ret" | "return" | "ent" | "enter" | "Enter"
  | "⏎" | "↩" | "↵" | "↲" | "⤶" | "⎆" | "⌤" | "␤" => some (.key .enter)
  | "bspc" | "bks" | "backspace" | "Backspace" | "␈" | "⌫" => some (.key .backspace)
  | "del" | "delete" | "Delete" | "␡" | "⌦" => some (.key .delete)
  | "spc" | "space" | "Space" | "␠" | "␣" => some (.key .space)
  | "left" | "lft" | "ArrowLeft" | "◀" | "←" => some (.key .left)
  | "rght" | "right" | "ArrowRight" | "▶" | "→" => some (.key .right)
  | "up" | "ArrowUp" | "▲" | "↑" => some (.key .up)
  | "down" | "ArrowDown" | "▼" | "↓" => some (.key .down)
  | "home" | "Home" | "⇤" | "⤒" | "↖" | "⇱" => some (.key .home)
  | "end" | "End" | "⇥" | "⤓" | "↘" | "⇲" => some (.key .«end»)
  | "pgup" | "pageup" | "PageUp" | "⇞" | "⎗" => some (.key .pageUp)
  | "pgdn" | "pagedown" | "PageDown" | "⇟" | "⎘" => some (.key .pageDown)
  | "caps" | "capslock" | "CapsLock" | "⇪" => some .capsLock
  -- The Unicode modifier spellings put the guillemet on the side the key is on:
  -- `‹⇧` is the left Shift and `⇧›` the right.  They are two characters, so the
  -- single-character fallback at the bottom never sees them.
  | "lsft" | "lshift" | "lshft" | "shft" | "sft" | "ShiftLeft" | "‹⇧" =>
      some (.modifier .shift .left)
  | "rsft" | "rshift" | "rshft" | "ShiftRight" | "RightShift" | "⇧›" =>
      some (.modifier .shift .right)
  | "lctl" | "lctrl" | "ctl" | "ControlLeft" | "‹⎈" | "‹⌃" => some (.modifier .ctrl .left)
  | "rctl" | "rctrl" | "ControlRight" | "⎈›" | "⌃›" => some (.modifier .ctrl .right)
  | "lalt" | "alt" | "AltLeft" | "‹⎇" | "‹⌥" => some (.modifier .alt .left)
  | "ralt" | "altgr" | "AltRight" | "⎇›" | "⌥›" | "⇮" => some (.modifier .alt .right)
  | "lmet" | "lmeta" | "met" | "MetaLeft" | "‹◆" | "‹⌘" | "‹❖" | "‹⊞" =>
      some (.modifier .super .left)
  | "rmet" | "rmeta" | "MetaRight" | "◆›" | "⌘›" | "❖›" | "⊞›" =>
      some (.modifier .super .right)
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
  Extra.every.map Code.extra

end Code

end CapslockMode.Kanata
