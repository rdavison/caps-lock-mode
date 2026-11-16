/-
# Tests for the kanata evaluator

`CapslockMode/Kanata/Layer.lean` proves the two general facts -- transparency
falls through to `defsrc`, and the identity config is the identity function.
What a proof cannot cover is a *table*: that the key names are the ones kanata
accepts, that the reader's three traps are handled, and that a config someone
actually runs parses to the thing they think it does.

So the fixture is the real `~/.config/kanata/kanata.kbd`, and the guards below
are about it rather than about a trimmed copy -- which is the reason the parser
records unmodelled forms instead of refusing the file that contains them.
-/
import CapslockMode
import Tests.Fixtures.Kanata

namespace CapslockMode.Tests.Kanata
open CapslockMode CapslockMode.Kanata

/-! ## The reader -/

/-- Render every top-level form, which is how two `Sexp`s are compared here:
`Sexp` has no `DecidableEq` (nested inductive), and the rendering reads better
in a failing guard anyway. -/
private def forms (s : String) : Option (List String) :=
  (read s).toOption.map (·.map Sexp.render)

#guard forms "(a b) (c)" == some ["(a b)", "(c)"]
#guard forms ";; a comment\n(a b) ;; another\n" == some ["(a b)"]

-- The trap: a *lone* `;` is an atom, and the real config puts one in four
-- layers.  Only `;;` starts a comment.
#guard forms "(a ; b)" == some ["(a ; b)"]
#guard forms "(a ;; b\n c)" == some ["(a c)"]

#guard forms "#| skipped |# (a)" == some ["(a)"]
#guard forms "(a #| mid |# b)" == some ["(a b)"]
#guard forms "(a (b (c)) d)" == some ["(a (b (c)) d)"]

-- `defchordsv2` ends in an empty list, so `()` has to read.
#guard forms "(defchordsv2 (lmet rmet) \\ 80 first-release ())"
  == some ["(defchordsv2 (lmet rmet) \\ 80 first-release ())"]

#guard forms "(a \"two words\" b)" == some ["(a \"two words\" b)"]

-- UTF-8 atoms, which a byte-oriented reader splits into invalid fragments.
#guard forms "(🔅 ▶⏸ S-,)" == some ["(🔅 ▶⏸ S-,)"]

-- `Sexp` has no `BEq`, so a failure is spelled as the absence of a result.
#guard (read "(a").toOption.isNone
#guard (read "a)").toOption.isNone
#guard (read "#| never ends").toOption.isNone
#guard (read "(a \"no end\n b)").toOption.isNone

/-! ## Key names -/

#guard Code.ofName? "caps" == Code.ofName? "CapsLock"
#guard Code.ofName? "lft" == Code.ofName? "left"
#guard Code.ofName? "left" == Code.ofName? "ArrowLeft"
#guard Code.ofName? "rght" == Code.ofName? "right"
#guard Code.ofName? "q" == Code.ofName? "KeyQ"
#guard Code.ofName? "7" == Code.ofName? "Digit7"
#guard Code.ofName? "f24" == some (.key (.f 24))
#guard Code.ofName? "F13" == some (.key (.f 13))
#guard Code.ofName? "f25" == none

-- The whole F-row of the fixture.
#guard Code.ofName? "🔅" == some (.extra .brightnessDown)
#guard Code.ofName? "🔆" == some (.extra .brightnessUp)
#guard Code.ofName? "◀◀" == some (.extra .prevTrack)
#guard Code.ofName? "▶⏸" == some (.extra .playPause)
#guard Code.ofName? "▶▶" == some (.extra .nextTrack)
#guard Code.ofName? "🔇" == some (.extra .mute)
#guard Code.ofName? "🔉" == some (.extra .volumeDown)
#guard Code.ofName? "🔊" == some (.extra .volumeUp)

-- The punctuation that is *not* in kanata's main match and comes from
-- `add_default_str_osc_mappings` instead.  All ten are in the fixture.
#guard ([",", ".", "/", ";", "'", "[", "]", "\\", "-", "="].all
  fun s => (Code.ofName? s).isSome)

-- `name` and `ofName?` are independent tables, so drift between them is caught
-- here rather than by a proof there is nothing to induct over.  `Extra` is the
-- half of `every` that could go stale silently, and `Extra.mem_every` proves it
-- has not.
#guard Code.every.all fun c => Code.ofName? c.name == some c

-- 111 before the table was taken from kanata's own source; the numpad, the
-- mouse, the Japanese input keys, the application keys and the ten `nop`s are
-- the difference.
#guard Code.every.length == 180

/-! ### Both spellings of a key, which is what many-to-one buys -/

#guard Code.ofName? "kp5" == Code.ofName? "Numpad5"
#guard Code.ofName? "kprt" == Code.ofName? "NumpadEnter"
#guard Code.ofName? "mlft" == Code.ofName? "mouseleft"
#guard Code.ofName? "102d" == Code.ofName? "IntlBackslash"
#guard Code.ofName? "ro" == Code.ofName? "IntlRo"
#guard Code.ofName? "nuhs" == Code.ofName? "NonUSPound"
#guard Code.ofName? "wkup" == Code.ofName? "WakeUp"
#guard Code.ofName? "bck" == Code.ofName? "BrowserBack"
#guard Code.ofName? "fwd" == Code.ofName? "BrowserForward"
#guard Code.ofName? "sls" == Code.ofName? "SpotLightSearch"
#guard Code.ofName? "mctl" == Code.ofName? "MissionControl"

/-! ### The Unicode aliases -/

#guard Code.ofName? "⌫" == Code.ofName? "bspc"
#guard Code.ofName? "⎋" == Code.ofName? "esc"
#guard Code.ofName? "↹" == Code.ofName? "tab"
#guard Code.ofName? "⏎" == Code.ofName? "ret"
#guard Code.ofName? "⌦" == Code.ofName? "del"
#guard Code.ofName? "␣" == Code.ofName? "spc"
#guard Code.ofName? "⇪" == Code.ofName? "caps"
#guard Code.ofName? "←" == Code.ofName? "left"
#guard Code.ofName? "→" == Code.ofName? "rght"
#guard Code.ofName? "⇞" == Code.ofName? "pgup"
#guard Code.ofName? "🌐" == Code.ofName? "fn"
#guard Code.ofName? "🔢₅" == Code.ofName? "kp5"

-- The modifier spellings put the guillemet on the side the key is on, which is
-- the only thing telling `‹⇧` from `⇧›`.
#guard Code.ofName? "‹⇧" == some (.modifier .shift .left)
#guard Code.ofName? "⇧›" == some (.modifier .shift .right)
#guard Code.ofName? "‹⌃" == some (.modifier .ctrl .left)
#guard Code.ofName? "⌃›" == some (.modifier .ctrl .right)
#guard Code.ofName? "‹⌥" == some (.modifier .alt .left)
#guard Code.ofName? "⇮" == some (.modifier .alt .right)
#guard Code.ofName? "‹⌘" == some (.modifier .super .left)
#guard Code.ofName? "⌘›" == some (.modifier .super .right)

/-! ### Five places kanata's table is not what it looks like

All five would be guesses if this file had not been read against
`parser/src/keys/mod.rs`, and all five would be wrong. -/

-- `kp=` is Clear.  The numpad `=` has no short name at all.
#guard Code.ofName? "kp=" == some (.extra .clear)
#guard Code.ofName? "clr" == some (.extra .clear)
#guard Code.ofName? "NumpadEqual" == some (.extra .kpEqual)

-- The ASCII `yen` is Backslash, because in some locales they share a position.
-- Only the Unicode spelling is the yen key.
#guard Code.ofName? "yen" == some (.key (.char '\\'))
#guard Code.ofName? "¥" == some (.extra .yen)

-- `+` is the *numpad* plus, not the shifted `=` of the digit row.
#guard Code.ofName? "+" == some (.extra .kpPlus)

-- `{` and `}` are the bracket keys, unshifted.
#guard Code.ofName? "{" == Code.ofName? "["
#guard Code.ofName? "}" == Code.ofName? "]"

-- The non-US backslash is `102d`.  `102nd` is evdev's name for the same key and
-- kanata does not take it, so neither does this.
#guard Code.ofName? "<" == some (.extra .intlBackslash)
#guard Code.ofName? "lsgt" == some (.extra .intlBackslash)
#guard Code.ofName? "nubs" == some (.extra .intlBackslash)
#guard Code.ofName? "102nd" == none

/-! ### The Japanese input block

`kana` is read as `KEY_HANGEUL` by a real macOS kanata and as
`KEY_KATAKANAHIRAGANA` by a Linux one.  This table is the platform-free build,
so it is the second. -/

#guard Code.ofName? "kana" == some (.extra .katakanaHiragana)
#guard Code.ofName? "katakanahiragana" == Code.ofName? "kana"
#guard Code.ofName? "hiragana" == some (.extra .hiragana)
#guard Code.ofName? "katakana" == some (.extra .katakana)
#guard Code.ofName? "henkan" == some (.extra .henkan)
#guard Code.ofName? "muhenkan" == some (.extra .muhenkan)
#guard Code.ofName? "eisu" == some (.extra .hanja)
#guard Code.ofName? "Lang2" == Code.ofName? "eisu"

/-! ## The bridge back to `PhysKey` -/

#guard Code.toPhys? (.key .esc) == some (.key .esc)
#guard Code.toPhys? .capsLock == some .capsLock

-- Left and right collapse: `PhysKey.mod` has nowhere to put the side.
#guard Code.toPhys? (.modifier .shift .left) == Code.toPhys? (.modifier .shift .right)

-- And the media keys have no image at all.  This `none` is the first thing a
-- `Machine` integration will have to answer.
#guard Code.toPhys? (.extra .mute) == none

/-! ## Aliases -/

private def aliasCfg : String :=
  "(defsrc a b c)\n(defalias x lctl  y (multi @x lsft))\n(deflayer base @y _ _)"

private def names (a : Action) : List String := a.keys.map Code.name

/-- What a position resolves to, in key names.  `none` is "no such position";
`some []` is a position that resolves to no keystroke at all. -/
private def at? (cfg : Cfg n) (st : St) (i : Nat) : Option (List String) :=
  (resolveAt? cfg st i).map names

#guard ((parseAs 3 aliasCfg).toOption.bind (fun c => resolveAt? c {} 0)).map names
  == some ["lctl", "lsft"]

-- Aliases resolve in one forward pass, so a later alias is not in scope.
#guard (parseAs 1 "(defsrc a)\n(defalias y @x  x lctl)\n(deflayer base @y)").toOption == none

/-! ## Width is a type, not a runtime surprise -/

#guard (parseAs 3 "(defsrc a b c)\n(deflayer base a b)").toOption == none

-- ... and the message says which layer and both counts.
#guard (match parseAs 3 "(defsrc a b c)\n(deflayer short a b)" with
        | .error m => m
        | .ok _ => "")
  == "(deflayer short) has 2 entries but (defsrc) has 3"

/-! ## Transparency falls to `defsrc`, not to the first layer -/

private def delegCfg (yes : String) : String :=
  s!"(defcfg delegate-to-first-layer {yes})\n(defsrc a b)\n\
     (deflayer one z _)\n(deflayer two _ _)"

-- Base is layer 1, and layer 0 says `z` at position 0.  With delegation off the
-- answer is `defsrc`; with it on, layer 0 joins the walk at the bottom.
#guard ((parseAs 2 (delegCfg "no")).toOption.bind (fun c => resolveAt? c { base := 1 } 0)).map names
  == some ["a"]
#guard ((parseAs 2 (delegCfg "yes")).toOption.bind (fun c => resolveAt? c { base := 1 } 0)).map names
  == some ["z"]

/-! ## The real config -/

/-- The fixture, parsed at the width its `defsrc` declares.

The fallback is deliberately a config of Caps Lock keys rather than something
plausible, so that a parse failure shows up as a wrong answer everywhere below
instead of quietly passing the identity guards. -/
private def real : Cfg 72 :=
  (parseAs 72 Fixture.kanataKbd).toOption.getD (Cfg.identity (Vector.replicate 72 .capsLock))

private def srcName (i : Nat) : String :=
  match pos? 72 i with
  | some p => (real.src[p.val]'p.isLt).name
  | none => "?"

#guard (parseAs 72 Fixture.kanataKbd).toOption.isSome

#guard real.layers.map (·.name) ==
  [ "aien-akl", "aien-shft", "inea-akl", "inea-shft", "nths-akl", "nths-shft"
  , "asdf-akl", "nav", "nav-ctl", "win", "rect", "rect-shft", "layers", "cmd-qwerty" ]

#guard real.options ==
  [ ("concurrent-tap-hold", "yes")
  , ("macos-dev-names-include",
     "(\"Apple Internal Keyboard / Trackpad\" \"Richard Davison’s Keyboard\" \
\"RF R1 8-9Xu\" \"Karabiner DriverKit VirtualHIDKeyboard 1.8.0\")") ]

-- `concurrent-tap-hold` is recorded and otherwise ignored; nothing here reads
-- it, because nothing here has a clock.
#guard real.delegateToFirstLayer == false

#guard (List.range 72).map srcName ==
  [ "esc", "f1", "f2", "f3", "f4", "f5", "f6", "f7", "f8", "f9", "f10", "f11", "f12"
  , "grv", "1", "2", "3", "4", "5", "6", "7", "8", "9", "0", "-", "=", "bspc"
  , "tab", "q", "w", "e", "r", "t", "y", "u", "i", "o", "p", "[", "]", "\\"
  , "caps", "a", "s", "d", "f", "g", "h", "j", "k", "l", ";", "'", "ret"
  , "lsft", "z", "x", "c", "v", "b", "n", "m", ",", ".", "/", "rsft"
  , "lctl", "lalt", "lmet", "spc", "rmet", "ralt" ]

/-! ## The identity config is the identity function -/

/-- One layer, all `_`, over the fixture's own `defsrc`. -/
private def idCfg : Cfg 72 := Cfg.identity real.src

-- `Layer.resolve_identity` proves this for every width and every `defsrc`.
-- This is the same statement on the 72 positions someone actually types on,
-- spelled out in key names so a failure says which position moved.
#guard (List.range 72).map (fun i => ((at? idCfg {} i).map (String.intercalate "+")).getD "?")
  == (List.range 72).map srcName

-- ... and it stays the identity with a layer held and the base moved, since a
-- config of nothing but `_` has nothing to find.
#guard (List.range 72).map
    (fun i => ((at? idCfg { base := 9, holds := [(3, { hold := [2] })] } i).map
      (String.intercalate "+")).getD "?")
  == (List.range 72).map srcName

/-! ## Transparency, on a config someone runs

The most misunderstood corner of kanata, stated where it is easiest to get
wrong.  `nav` is layer 7 and its second row is all `_`.  Position 13 is `grv` in
`defsrc` and `@grv-mode` in layer 0 (`aien-akl`). -/

#guard real.layerIx? "nav" == some 7
#guard at? real { base := 7 } 13 == some ["grv"]
#guard at? real {} 13 == some []        -- layer 0 says `@grv-mode`, which is blocked

-- With delegation on, layer 0 joins the walk and the answer changes to the
-- `tap-hold` -- which is a decision still open rather than a keystroke, so it
-- names no codes and refuses nothing.
#guard (resolveAt? { real with delegateToFirstLayer := true } { base := 7 } 13).map (·.blocked)
  == some []
#guard ((resolveAt? { real with delegateToFirstLayer := true } { base := 7 } 13).map
  (·.tapHold.isSome)) == some true

/-! ## The fixture's characteristic idiom

`@aien-shft` is `(multi lsft (layer-while-held aien-shft))`, at positions 54 and
65 -- the two Shift keys.  Holding it presses Shift *and* switches layer, and
the layer overrides a handful of positions and leaves the rest transparent. -/

private def held54 : St :=
  ((runIx real {} [(.down, 54)]).toOption.map (·.1)).getD {}

#guard (runIx real {} [(.down, 54)]).toOption.map (fun r => render r.2) == some "down lsft"
#guard held54.holds.map (·.1) == [54]

-- Position 55 is `,` in the base layer and `;` in `aien-shft`.
#guard at? real {} 55 == some [","]
#guard at? real held54 55 == some [";"]

-- Position 59 is `_` in `aien-shft`, so it falls through to the base layer's
-- `q` -- the override-a-few-and-fall-through half of the idiom.
#guard at? real held54 59 == some ["q"]

-- Position 71 is `_` in `aien-shft` and `rmet` in the base layer.
#guard at? real held54 71 == at? real {} 71
#guard at? real {} 71 == some ["rmet"]

-- Holding Shift, typing position 55, and letting go.  The `,` at the end is the
-- same position after the release, back to what the base layer says.
#guard (runIx real {} [(.down, 54), (.down, 55), (.up, 55), (.up, 54), (.down, 55)]).toOption.map
    (fun r => render r.2)
  == some "down lsft down ; up ; up lsft down ,"

/-! ## The layer stack -/

private def holdCfg : String :=
  "(defsrc a b c)\n(deflayer base (layer-while-held alt) _ _)\n(deflayer alt _ x _)"

private def toggleCfg : String :=
  "(defsrc a b c)\n(deflayer base (layer-toggle alt) _ _)\n(deflayer alt _ x _)"

-- `layer-toggle` is not a synonym noted in a comment: it parses to the *same*
-- `Action`, so it cannot drift into being a latch.
#guard (parseAs 3 holdCfg).toOption.map (·.layers)
  == (parseAs 3 toggleCfg).toOption.map (·.layers)

private def holdReal : Cfg 3 :=
  (parseAs 3 holdCfg).toOption.getD (Cfg.identity (Vector.replicate 3 .capsLock))

private def afterHold : St := ((runIx holdReal {} [(.down, 0)]).toOption.map (·.1)).getD {}

#guard (resolveAt? holdReal afterHold 1).map names == some ["x"]
#guard (resolveAt? holdReal (release afterHold (0 : Fin 3)).1 1).map names == some ["b"]

-- Holding a layer key emits nothing of its own; it is the layer that does the
-- work.
#guard (runIx holdReal {} [(.down, 0)]).toOption.map (fun r => render r.2) == some ""

private def switchCfg : Cfg 2 :=
  (parseAs 2 "(defsrc a b)\n(deflayer base (layer-switch other) _)\n(deflayer other _ y)").toOption.getD
    (Cfg.identity (Vector.replicate 2 .capsLock))

private def afterSwitch : St :=
  ((runIx switchCfg {} [(.down, 0), (.up, 0)]).toOption.map (·.1)).getD {}

-- A `layer-switch` survives its own release.  That is the whole difference
-- between it and `layer-while-held`, and the reason `release_undoes_press` has
-- to assume there was no switch.
#guard afterSwitch.base == 1
#guard afterSwitch.holds == []
#guard (resolveAt? switchCfg afterSwitch 1).map names == some ["y"]

-- A release of a position that was never pressed is a no-op, not a failure.
#guard (runIx switchCfg {} [(.up, 1)]).toOption.map (fun r => (r.1, render r.2)) == some ({}, "")

/-! ## Modifier prefixes -/

private def chordCfg : Cfg 3 :=
  (parseAs 3 "(defsrc a b c)\n(deflayer base S-, C-S-x AG-4)").toOption.getD
    (Cfg.identity (Vector.replicate 3 .capsLock))

#guard (resolveAt? chordCfg {} 0).map names == some ["lsft", ","]
#guard (resolveAt? chordCfg {} 1).map names == some ["lctl", "lsft", "x"]
#guard (resolveAt? chordCfg {} 2).map names == some ["ralt", "4"]

-- A repeated modifier is an error, as it is in kanata.
#guard (parseAs 1 "(defsrc a)\n(deflayer base S-S-x)").toOption == none

-- The key table is consulted before the chord parser, so a key whose name
-- starts with a modifier spelling is still that key.  `S-` is upper case and no
-- key name is, which is why this can never bite in practice.
#guard Code.ofName? "min" == some (.key (.char '-'))

/-! ## `use-defsrc`, and how it differs from `_`

Both name the `defsrc` key, and they are not the same thing: `_` keeps walking
and takes whatever the next layer down says, `use-defsrc` stops.  They agree
whenever the layers below happen to be transparent too, which is why the test
below is set up so that they do not. -/

private def srcCfg : Cfg 2 :=
  (parseAs 2 "(defsrc a b)\n(deflayer base x y)\n(deflayer over use-defsrc _)").toOption.getD
    (Cfg.identity (Vector.replicate 2 .capsLock))

/-- Layer 1 (`over`) held above layer 0 (`base`), so the walk is `over`, `base`,
`defsrc` and all three say something different. -/
private def overHeld : St := { base := 0, holds := [(9, { hold := [1] })] }

-- Position 0 is `use-defsrc` in `over`: it takes `defsrc`'s `a` and never sees
-- the `x` one layer down.
#guard at? srcCfg overHeld 0 == some ["a"]
-- Position 1 is `_` in `over`: it keeps looking and finds `base`'s `y`.
#guard at? srcCfg overHeld 1 == some ["y"]
-- With nothing held both are the base layer's own entries, which is the case
-- where the two would have looked alike.
#guard at? srcCfg {} 0 == some ["x"]
#guard at? srcCfg {} 1 == some ["y"]

-- The flag is gone from the resolved action: `resolve` is where `use-defsrc`
-- stops existing, and running it twice cannot press `defsrc` twice.
#guard (resolveAt? srcCfg overHeld 0).map (·.src) == some false

private def srcAliasCfg : Cfg 2 :=
  (parseAs 2 "(defsrc a b)\n(defalias u use-defsrc)\n(deflayer base @u @u)").toOption.getD
    (Cfg.identity (Vector.replicate 2 .capsLock))

-- The same alias on two positions has to mean two different keys, which is why
-- `use-defsrc` cannot be resolved at parse time even though `defsrc` is already
-- known by then.
#guard at? srcAliasCfg {} 0 == some ["a"]
#guard at? srcAliasCfg {} 1 == some ["b"]

-- Inside a `multi` it lands after the codes written beside it -- the third
-- stated cost of `Action` being a flat record.
#guard ((parseAs 1 "(defsrc a)\n(deflayer base (multi lsft use-defsrc))").toOption.bind
  (fun c => resolveAt? c {} 0)).map names == some ["lsft", "a"]

-- It is an action and not a key name, so `defsrc` will not take it.
#guard (parseAs 1 "(defsrc use-defsrc)\n(deflayer base a)").toOption == none

/-! ## `unicode`

A character is not a key.  `(unicode x)` types `x` whatever the layout would
have made of the `x` position, so it produces no `Code` at all -- and no
`Event`, because an `Event` is a code going down and coming up and a typed
character has no release to give back. -/

private def uniCfg : Cfg 3 :=
  (parseAs 3 "(defsrc a b c)\n\
    (deflayer base (unicode U+1F686) (🔣 x) (multi lsft (unicode U+00E9)))").toOption.getD
    (Cfg.identity (Vector.replicate 3 .capsLock))

#guard (resolveAt? uniCfg {} 0).map (·.text) == some [Char.ofNat 0x1F686]
#guard (resolveAt? uniCfg {} 1).map (·.text) == some ['x']
#guard (resolveAt? uniCfg {} 2).map (fun a => (names a, a.text))
  == some (["lsft"], [Char.ofNat 0xE9])

-- `(unicode x)` is the character and not the `x` key.
#guard at? uniCfg {} 1 == some []

-- Pressing emits the codes and not the text.  The text is read off the action,
-- which is the same seam a `Machine` integration has to fill anyway: `Key` has
-- no `é` either.
#guard (runIx uniCfg {} [(.down, 2), (.up, 2)]).toOption.map (fun r => render r.2)
  == some "down lsft up lsft"

-- A surrogate is not a character, an ordinary word is not a codepoint, and
-- kanata takes exactly one argument.
#guard (parseAs 1 "(defsrc a)\n(deflayer base (unicode U+D800))").toOption == none
#guard (parseAs 1 "(defsrc a)\n(deflayer base (unicode abc))").toOption == none
#guard (parseAs 1 "(defsrc a)\n(deflayer base (unicode))").toOption == none
#guard (parseAs 1 "(defsrc a)\n(deflayer base (unicode a b))").toOption == none

/-! ## Forms this evaluator refuses -/

#guard real.blocked ==
  [ { form := "defchordsv2", site := "top level", reason := .clock }
  , { form := "one-shot", site := "alias @rect", reason := .clock }
  , { form := "macro", site := "alias @lchev", reason := .clock }
  , { form := "macro", site := "alias @rchev", reason := .clock }
  , { form := "lrld", site := "deflayer layers", reason := .world } ]

-- Four of the five wait on a timestamp and one does not, which is the whole
-- reason the reason is recorded.
#guard (real.blocked.filter (·.reason == .world)).map (·.form) == ["lrld"]
#guard real.blocked.all (·.reason != .history)

#guard Blocked.describe { form := "lrld", site := "deflayer layers", reason := .world }
  == "lrld in deflayer layers (needs the world outside the keyboard)"

-- `tap-hold` is modelled now, so neither `@grv-mode` nor `@cap` is refused.
-- Asserted as the new truth rather than as a smaller number, so that a
-- regression reads as "tap-hold came back" instead of "the count moved".
#guard real.blocked.all (·.form != "tap-hold")

-- What is left of the clock frontier, and why each one is still on it: a
-- one-shot is a latch with its own expiry, a macro has to emit *in the future*,
-- and a chord has several keys pending at once.  A timestamp fixes none of
-- those; each needs a timer, or a `pending` that is a list.
#guard (real.blocked.map (·.form)).eraseDups
  == ["defchordsv2", "one-shot", "macro", "lrld"]

-- `parseStrict` refuses the file, and says what it refused it for.
#guard ((match parseStrict Fixture.kanataKbd with | .error m => m | .ok _ => "")
  |>.splitOn "defchordsv2").length == 2

-- Pressing a blocked position is a named failure, not a wrong keystroke.
-- Position 18 is `5`, and layer 12 (`layers`) says `lrld`.
#guard (match runIx real { base := 12 } [(.down, 18)] with | .error m => m | .ok _ => "")
  == "position 18 resolves to lrld, which this evaluator does not model"

/-! ### Tap-hold, on the config it was built for

`@grv-mode` is `(tap-hold 200 200 grv (layer-while-held layers))` at position 13
of four layers.  A press says nothing at all -- that is the one press in this
evaluator that emits nothing and records a decision instead -- and the next
event decides it. -/

private def thRun (st : St) (evs : List (Dir × Nat × Nat)) : String :=
  ((runIxAt real st evs).toOption.map (fun r => render r.2)).getD "<error>"

-- A press alone emits nothing and leaves the decision open.
#guard thRun {} [(.down, 13, 0)] == ""
#guard ((runIxAt real {} [(.down, 13, 0)]).toOption.map (·.1.pending.isSome)) == some true

-- Released inside the window: the tap action, pressed and released.
#guard thRun {} [(.down, 13, 0), (.up, 13, 80)] == "down grv up grv"

-- Released after it: the hold.  Here the hold is a bare `layer-while-held`, so
-- it names no codes and emits nothing -- which is what kanata is observably
-- doing too.
#guard thRun {} [(.down, 13, 0), (.up, 13, 500)] == ""

-- Interrupted by another key: the hold settles *first*, so position 15 resolves
-- against a stack with `layers` on it.  Layer 12 says `@nths-akl` there, which
-- is `(layer-switch nths-akl)` -- layer 4.  This one guard is the whole
-- mechanism of "hold the key, then type".
#guard ((runIxAt real {} [(.down, 13, 0), (.down, 15, 50)]).toOption.map (·.1.base))
  == some 4

-- An unstamped stream is one on which nothing ever times out, so every
-- tap-hold on it is a tap.  That is what keeps `runIx` meaning what it meant.
#guard (runIx real {} [(.down, 13), (.up, 13)]).toOption.map (fun r => render r.2)
  == some "down grv up grv"

/-! ### Refused, not unrecognised

Each of these used to fail as an *unknown atom*, so the whole file stopped
loading and the message said "unrecognised" where the truth was "supported by
kanata, not modelled here, and here is what it would take".  What the guards
below assert is the difference: the config parses, and what it parses to names
the form and the reason. -/

/-- The one-position config whose only entry is `e`, reduced to what it
refused. -/
private def refused (e : String) : Option (List (String × Reason)) :=
  (parseAs 1 s!"(defsrc a)\n(deflayer base {e})").toOption.map
    (fun c => c.blocked.map (fun b => (b.form, b.reason)))

-- The control for every guard below: a name in none of the lists is still an
-- unknown atom and still stops the file loading, so `refused` saying `some`
-- means something.
#guard refused "nosuchform" == none
#guard refused "(nosuchform x)" == none

-- Needs a history: `rpt` repeats the last action, and the dynamic macros replay
-- a recording of one.  Nothing in `St` remembers either.
#guard refused "rpt" == some [("rpt", .history)]
#guard refused "rpt-any" == some [("rpt-any", .history)]
#guard refused "dynamic-macro-record-stop" == some [("dynamic-macro-record-stop", .history)]
#guard refused "(dynamic-macro-record 1)" == some [("dynamic-macro-record", .history)]
#guard refused "(dynamic-macro-play 1)" == some [("dynamic-macro-play", .history)]

-- `fork` and `switch` look like present-tense tests of what is held and are
-- not: kanata answers them against its own output state.  A clock would not
-- help, which is why they are not filed with `tap-hold`.
#guard refused "(fork a b (c))" == some [("fork", .history)]
#guard refused "(switch (a) b break)" == some [("switch", .history)]

-- Needs a clock: a sequence leader's first obligation is the timeout.
#guard refused "sldr" == some [("sldr", .clock)]
#guard refused "scnl" == some [("scnl", .clock)]

-- Needs the world: a pointer is no more part of a keyboard than `lrld`'s file
-- is, and no `Code` could carry a click out.
#guard refused "mlft" == some [("mlft", .world)]
#guard refused "mwu" == some [("mwu", .world)]
#guard refused "(mwheel-up 50 120)" == some [("mwheel-up", .world)]
#guard refused "(movemouse-up 1 1)" == some [("movemouse-up", .world)]
#guard refused "(setmouse 100 100)" == some [("setmouse", .world)]

-- The whole set, asserted as "records exactly one refusal" rather than one
-- guard each, because the interesting property is that none of them is an
-- unknown atom any more.
#guard [ "rpt", "repeat", "rpt-key", "rpt-any", "sldr", "scnl"
       , "mlft", "mouseleft", "mrgt", "mmid", "mbck", "mfwd"
       , "mltp", "mrtp", "mmtp", "mftp", "mbtp"
       , "mwu", "mwd", "mwl", "mwr", "mvmt"
       , "dynamic-macro-record-stop"
       , "(fork a b (c))", "(switch (a) b break)"
       , "(dynamic-macro-record 1)", "(dynamic-macro-play 1)"
       , "(dynamic-macro-record-stop-truncate 1)"
       , "(mwheel-down 50 120)", "(mwheel-accel-up 1 2 3 4)"
       , "(movemouse-left 1 1)", "(movemouse-accel-right 1 1 1 1)"
       , "(movemouse-speed 50)", "(setmouse 1 1)" ].all
  fun e => (refused e).map (·.length) == some 1

-- The mouse names are `Code`s too, and in `defsrc` that is what they are.  The
-- action table runs first and `defsrc` does not consult it, which is kanata's
-- own reading of the same atom twice.
#guard ((parseAs 1 "(defsrc mlft)\n(deflayer base _)").toOption.bind
  (fun c => resolveAt? c {} 0)).map names == some ["mlft"]

-- Pressing one is the same named refusal a `tap-hold` is.
#guard (match (parseAs 1 "(defsrc a)\n(deflayer base mlft)") with
        | .ok c => (match runIx c {} [(.down, 0)] with | .error m => m | .ok _ => "")
        | .error _ => "")
  == "position 0 resolves to mlft, which this evaluator does not model"

-- An unknown atom is a hard error: a typo must never be skipped.
#guard (parseAs 1 "(defsrc a)\n(deflayer base nosuchkey)").toOption == none
#guard (parseAs 1 "(defsrc a)\n(deflayer base (nosuchform x))").toOption == none
#guard (read "(deftemplate t () a)").toOption.isSome
#guard (parseAs 1 "(defsrc a)\n(deftemplate t () a)\n(deflayer base a)").toOption == none

-- `XX` is a real no-op and a different thing from `_`: it stops the walk.
#guard (parseAs 2 "(defsrc a b)\n(deflayer base XX _)").toOption.bind (fun c => resolveAt? c {} 0)
  == some {}
#guard ((parseAs 2 "(defsrc a b)\n(deflayer base XX _)").toOption.bind
  (fun c => resolveAt? c {} 1)).map names == some ["b"]

end CapslockMode.Tests.Kanata
