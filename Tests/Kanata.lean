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
-- here rather than by a proof there is nothing to induct over.
#guard Code.every.all fun c => Code.ofName? c.name == some c

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

private def at? (cfg : Cfg 72) (st : St) (i : Nat) : Option (List String) :=
  (resolveAt? cfg st i).map names

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
-- `tap-hold` -- which is then a refusal rather than a keystroke.
#guard (resolveAt? { real with delegateToFirstLayer := true } { base := 7 } 13).map (·.blocked)
  == some ["tap-hold"]

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

/-! ## Forms this evaluator refuses -/

#guard real.blocked ==
  [ { form := "defchordsv2", site := "top level" }
  , { form := "tap-hold", site := "alias @grv-mode" }
  , { form := "tap-hold", site := "alias @cap" }
  , { form := "one-shot", site := "alias @rect" }
  , { form := "macro", site := "alias @lchev" }
  , { form := "macro", site := "alias @rchev" }
  , { form := "lrld", site := "deflayer layers" } ]

-- `@grv-mode` is used at position 13 of four different layers and reported
-- once, at the alias that defines it.
#guard (real.blocked.filter (·.form == "tap-hold")).length == 2

-- `parseStrict` refuses the file, and says what it refused it for.
#guard ((match parseStrict Fixture.kanataKbd with | .error m => m | .ok _ => "")
  |>.splitOn "defchordsv2").length == 2

-- Pressing a blocked position is a named failure, not a wrong keystroke.
#guard (match runIx real {} [(.down, 13)] with | .error m => m | .ok _ => "")
  == "position 13 resolves to tap-hold, which this evaluator does not model"

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
