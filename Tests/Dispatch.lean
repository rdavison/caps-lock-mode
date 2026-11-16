/-
# Tests for the mode-to-backend dispatcher

`CapslockMode/Dispatch.lean` proves the general facts: the identity config is
transparent through the dispatcher, a pass-through is matched on release, and
binding vi is binding `step`.  What a proof does not cover is that the
*assembly* is the one a user would recognise -- that a real config's layers
apply, that vi still behaves like vi through the new layer, and that a refused
form is audible rather than silent.

Every position below is given as its `defsrc` code, because that is what the
dispatcher takes: a physical position, not a key.  So "press the `z` key" means
the position whose bare legend is `z`, which in this config is where `,` lives.
-/
import CapslockMode
import Tests.Fixtures.Kanata

namespace CapslockMode.Tests.Dispatch
open CapslockMode CapslockMode.Dispatch

/-- The fixture, at the width its `defsrc` declares.  The fallback is a config
of Caps Lock keys rather than something plausible, so a parse failure shows up
as a wrong answer everywhere below instead of quietly passing. -/
private def real : Kanata.Cfg 72 :=
  (Kanata.parseAs 72 Kanata.Fixture.kanataKbd).toOption.getD
    (Kanata.Cfg.identity (Vector.replicate 72 .capsLock))

/-- The `defsrc` code at a position, which is what a caller hands `dispatch`. -/
private def at? (i : Nat) : Kanata.Code :=
  match Kanata.pos? 72 i with
  | some p => real.src[p.val]'p.isLt
  | none => .capsLock

/-- Feed a stream of positions through the dispatcher.  Named rather than called
directly because `CapslockMode.run` is the machine's own `run` and the two are
ambiguous in a file that has both open. -/
private def go {σ : Type} (back : Step σ) (w : World σ) (evs : List (Dir × Kanata.Code)) :
    World σ × List Effect :=
  Dispatch.run back w evs

/-- The codes a run put back on the wire, in the notation `Tests/Kanata.lean`
uses. -/
private def codes {σ : Type} (r : World σ × List Effect) : String :=
  Kanata.render (Effect.codes r.2)

/-- The keystrokes a run synthesised, in the notation `Tests/Basic.lean` uses. -/
private def keys {σ : Type} (r : World σ × List Effect) : String :=
  renderEvents (Effect.emitted r.2)

/-- `go`, with a millisecond stamp on each edge.  `go` is the all-zero case,
which is why it keeps its meaning: an unstamped stream is one on which nothing
ever times out. -/
private def goAt {σ : Type} (back : Step σ) (w : World σ)
    (evs : List (Dir × Kanata.Code × Nat)) : World σ × List Effect :=
  Dispatch.runAt back w evs

/-! ## The identity config bound to `insert`

`dispatch_identity_transparent` proves this for every width and every `defsrc`.
The guards below are the same statement on the 72 positions someone actually
types on, so a failure says which position moved. -/

private def idBack : Step (State × Kanata.St) := Dispatch.identity real.src

/-- Insert mode, and therefore -- by the binding, and not by a second field
saying so -- the evaluator.  `World.backend` has no default, because `σ` is a
parameter and a default would need `Inhabited σ` in the signature. -/
private def idW : World (State × Kanata.St) := { backend := ({}, {}) }

-- The module's claim that a backend can be a *parameter* rests on `World σ`
-- still deriving all three instances given them for `σ`.  These three lines
-- check that rather than leaving it asserted: each one fails to compile if the
-- corresponding instance is not there.
#guard idW == idW
#guard (reprStr idW).length > 0
#guard (default : World (State × Kanata.St)).through == []

-- Position 41 is `caps`, which is the mode key: it is the one position that is
-- never transparent, because it is how you get back out.  Everything else
-- passes through as itself.
#guard ((List.range 72).filter (· != 41)).all fun i =>
  (dispatch idBack idW .down (at? i)).2 == [Effect.emitCode ⟨.down, at? i⟩]

-- Press and release, which is where a lossy conversion would show up as a
-- stuck key rather than as a wrong keystroke.
#guard codes (go idBack idW [(.down, at? 55), (.up, at? 55)]) == "down z up z"

-- The volume keys have no `PhysKey` and no `Key` at all, and they still cross
-- unchanged.  This is the case sketch B would have dropped: `Code.toPhys?` has
-- no image for `🔊`, so a machine that converted on the way in could not have
-- emitted it on the way out.  (`volu` is kanata's canonical spelling of the
-- position the fixture writes as `🔊`.)
#guard codes (go idBack idW [(.down, .extra .volumeUp), (.up, .extra .volumeUp)])
  == "down volu up volu"

-- Nothing but `emitCode`: no vi keystrokes, no mode change, no refusals.
#guard (go idBack idW ((List.range 72).filter (· != 41) |>.map fun i => (Dir.down, at? i))).2
  == ((List.range 72).filter (· != 41)).map fun i => Effect.emitCode ⟨.down, at? i⟩

/-! ## A real config bound to `insert` -/

private def realBack : Step (State × Kanata.St) := modal {} [.insert] real

private def realW : World (State × Kanata.St) := { backend := ({}, {}) }

-- Position 55's bare legend is `z`; layer 0 (`aien-akl`) says `,` there.
#guard codes (go realBack realW [(.down, at? 55), (.up, at? 55)]) == "down , up ,"

-- A position `defsrc` does not mention is not intercepted, which is kanata's
-- own rule.  The numpad is nowhere in this 72-key config.
#guard (dispatch realBack realW .down (.extra .kp5)).2
  == [Effect.emitCode ⟨.down, .extra .kp5⟩]

/-! ### `@aien-shft`, the fixture's characteristic idiom

`(multi lsft (layer-while-held aien-shft))`, at positions 54 and 65 -- the two
Shift keys.  Holding it presses Shift *and* pushes a layer that overrides a
handful of positions and leaves the rest transparent. -/

-- Hold Shift, type position 55, let go, type it again.  `;` while held, `,`
-- after -- and the same `up lsft` the press asked for.
#guard codes (go realBack realW
    [(.down, at? 54), (.down, at? 55), (.up, at? 55), (.up, at? 54), (.down, at? 55)])
  == "down lsft down ; up ; up lsft down ,"

-- The fall-through half of the idiom: position 59 is `_` in `aien-shft`, so it
-- is still the base layer's `q` while Shift is held.
#guard codes (go realBack realW [(.down, at? 54), (.down, at? 59)])
  == "down lsft down q"

/-! ### `layer-switch` is an effect, not a keystroke -/

-- Base layer 12 is `layers`, where position 15 says `@nths-akl`, which is
-- `(layer-switch nths-akl)`.  `nths-akl` is layer 4.
#guard (dispatch realBack { backend := ({}, { base := 12 }) } .down (at? 15)).2
  == [Effect.setBase 4]
#guard (dispatch realBack { backend := ({}, { base := 12 }) } .down (at? 15)).1.backend.2.base
  == 4

/-! ### A refused form is audible

The alternative -- emitting nothing -- is the failure that hides, which is why
`Cfg.blocked` records a form instead of the parser refusing the file. -/

-- Position 69 is `spc`, and layer 9 (`win`) says `@rect`, a one-shot: a latch
-- with its own expiry, which a timestamp does not buy.
#guard (dispatch realBack { backend := ({}, { base := 9 }) } .down (at? 69)).2
  == [Effect.refused "one-shot" .clock]

/-! ### Tap-hold, through the dispatcher

Position 13 is `grv`, and layer 0 says `@grv-mode`, which is
`(tap-hold 200 200 grv (layer-while-held layers))`.  These are the same cases
`Tests/Kanata.lean` guards one level down, re-stated here because the
dispatcher is where the clock actually arrives -- `Edge.time`, off the wire. -/

-- Tapped: a backtick, and nothing else.
#guard codes (goAt realBack realW [(.down, at? 13, 0), (.up, at? 13, 80)])
  == "down grv up grv"

-- A press on its own says nothing at all.  This is the one press in the
-- evaluator that emits nothing and records a decision instead.
#guard codes (goAt realBack realW [(.down, at? 13, 0)]) == ""

-- Held past the window and then a key: the hold settles first, so the `layers`
-- layer is live and position 15 resolves there to `@nths-akl`, a layer switch.
#guard (goAt realBack realW [(.down, at? 13, 0), (.down, at? 15, 300)]).2
  == [Effect.setBase 4]

-- The same inside the window.  An interrupting press resolves a tap-hold as a
-- hold whatever the clock says -- this evaluator's one divergence from
-- kanata's plain `tap-hold`, written down beside `clockForms`.
#guard (goAt realBack realW [(.down, at? 13, 0), (.down, at? 15, 50)]).2
  == [Effect.setBase 4]

-- An unstamped stream is one on which nothing times out, so the same two edges
-- through `go` are a tap.
#guard codes (go realBack realW [(.down, at? 13), (.up, at? 13)]) == "down grv up grv"

/-! ### The mode key, with a hold reading

`Config.toggleHold` gives Caps Lock a second reading: tapped it still moves the
mode, held it is an ordinary position and the config decides what it means.  In
this fixture position 41 is `caps` and layer 0 binds it to `@ctl`, which is
`(multi lctl (layer-while-held cmd-qwerty))` -- Ctrl, plus a layer that puts the
shortcuts back on their QWERTY positions.

The press is dispatched eagerly and the *release* decides, which is why holding
and then typing needs no retroactive machinery: the layer is already pushed by
the time the next key resolves. -/

private def TH : Config := { toggleHold := some 200 }
private def thBack : Step (State × Kanata.St) := modal TH [.insert] real

-- Tapped: the mode moves, exactly as it does with no hold reading at all.
#guard (goAt thBack realW [(.down, .capsLock, 0), (.up, .capsLock, 80)]).1.backend.1.mode
  == Mode.normal

private def heldThenS : List (Dir × Kanata.Code × Nat) :=
  [(.down, .capsLock, 0), (.down, at? 43, 300), (.up, at? 43, 310), (.up, .capsLock, 400)]

-- Held: the mode does not move...
#guard (goAt thBack realW heldThenS).1.backend.1.mode == Mode.insert

-- ... and `cmd-qwerty` is live underneath it.  Position 43 is `s` in `defsrc`,
-- `i` in layer 0 (aien) and `s` again in `cmd-qwerty`, so the emitted code is
-- the discriminator between "the layer pushed" and "it did not".
#guard codes (goAt thBack realW heldThenS) == "down lctl down s up s up lctl"

-- Without the hold reading the same stream is the mode key and then vi: the
-- `@ctl` binding is never reached, and position 43 types nothing in normal
-- mode.
#guard codes (goAt realBack realW heldThenS) == ""

-- And with no config bound at all, Caps Lock still types nothing: the promise
-- `Invariants.prelude_capsLock_silent` makes, which `toggleHold = none` is why
-- this module did not have to weaken.
#guard (dispatch realBack realW .down .capsLock).2 == [Effect.enter .normal]

-- Position 18 is `5`, and layer 12 (`layers`) says `lrld`: timeless, and still
-- refused, because it wants a file rather than a clock.
#guard (dispatch realBack { backend := ({}, { base := 12 }) } .down (at? 18)).2
  == [Effect.refused "lrld" .world]

/-! ### `unicode` is a third channel

`Kanata.press` deliberately does not emit `Action.text`: a character has no
release to give back, so putting it in `keys` would make letting go of the key
un-type it.  So the dispatcher carries it separately rather than dropping it. -/

private def uniCfg : Kanata.Cfg 2 :=
  (Kanata.parseAs 2
      "(defsrc a b)\n(deflayer base (unicode 🚆) (multi lsft (unicode x)))").toOption.getD
    (Kanata.Cfg.identity (Vector.replicate 2 .capsLock))

private def uniBack : Step (State × Kanata.St) := modal {} [.insert] uniCfg
private def uniW : World (State × Kanata.St) := { backend := ({}, {}) }

#guard (dispatch uniBack uniW .down (.key (.char 'a'))).2
  == [Effect.emitText [Char.ofNat 0x1F686]]
#guard (dispatch uniBack uniW .down (.key (.char 'b'))).2
  == [Effect.emitCode ⟨.down, .modifier .shift .left⟩, Effect.emitText ['x']]

/-! ## The vi backend, through the dispatcher

`viAlone` is vi behind the guards and paired with `nothing` -- the shape the
project has today, assembled rather than written into the machine.
`viAlone_down` proves its state and keystrokes are `step`'s; these guards are
that they are the ones `Tests/Basic.lean` expects. -/

private def N : Config := { startMode := .normal }
private def viBack : Step (State × Unit) := viAlone N
private def viW : World (State × Unit) := { backend := ({ mode := .normal }, ()) }
private def viInsertW : World (State × Unit) := { backend := ({}, ()) }

#guard keys (go viBack viW [(.down, .key (.char 'd')), (.down, .key (.char 'd'))])
  == "home shift+down del"
#guard keys (go viBack viW [(.down, .key (.char '3')), (.down, .key (.char 'd')),
    (.down, .key (.char 'd'))])
  == "home shift+down shift+down shift+down del"
#guard keys (go viBack viW [(.down, .key (.char 'h'))]) == "left"
#guard keys (go viBack viW [(.down, .key (.char 'w'))]) == "ctrl+right"

-- Shift is a *position* here, so the upper-case commands only work if the
-- dispatcher keeps a modifier level and applies the layout to it.  `D` is
-- `shift+end del`; without `Quartz.applyShift` this would be `d`'s answer.
#guard keys (go viBack viW [(.down, .modifier .shift .left), (.down, .key (.char 'd'))])
  == "shift+end del"

-- `escapeToNormal` is a vi affordance, so it belongs to the vi *backend* and
-- not to the dispatcher.  Bound to vi, `Esc` in insert mode leaves insert mode;
-- bound to the evaluator, `Esc` is just a position and passes through.  That is
-- a real consequence of the binding rather than an oversight, and this is where
-- it is written down.
#guard (dispatch viBack viInsertW .down (.key .esc)).2
  == [Effect.enter .normal]
#guard (dispatch realBack realW .down (at? 0)).2 == [Effect.emitCode ⟨.down, .key .esc⟩]

-- Insert mode is still vi's when nothing binds it away, and still transparent.
#guard keys (go viBack viInsertW
    [(.down, .key (.char 'h')), (.down, .key (.char 'i'))])
  == "h i"

-- A position vi cannot name, with no evaluator behind it: nobody claims it, so
-- the dispatcher passes it through and remembers that it did.
#guard codes (go viBack viInsertW
    [(.down, .extra .volumeUp), (.up, .extra .volumeUp)])
  == "down volu up volu"
#guard (dispatch viBack viInsertW .down (.extra .volumeUp)).1.through
  == [Kanata.Code.extra .volumeUp]

-- ... and a release it never passed through emits nothing, which is
-- `up_only_if_through`.
#guard (dispatch viBack viInsertW .up (.extra .volumeUp)).2 == []

/-! ## `enter` announces a mode change

It carries no backend, because there is no backend tag to carry: which backend
owns the keyboard is `modal`'s function of the mode, re-decided on every edge. -/

-- The mode key is the guards', so it works while a kanata config owns the
-- keyboard -- which is the point of its having been hoisted.
#guard (dispatch realBack realW .down .capsLock).2 == [Effect.enter .normal]
#guard (dispatch realBack realW .down .capsLock).1.backend.1.mode == Mode.normal

-- ... and back again, to the mode the evaluator is bound to.
#guard (dispatch realBack (dispatch realBack realW .down .capsLock).1 .down .capsLock).2
  == [Effect.enter .insert]

-- A vi mode change moves the binding with it, without anything saying so twice:
-- `i` in normal mode enters insert, which `realBack` binds to the evaluator.
#guard (dispatch realBack { backend := ({ mode := .normal }, {}) } .down (.key (.char 'i'))).2
  == [Effect.enter .insert]

-- A command that does not move the mode says nothing about the binding.
#guard (dispatch realBack { backend := ({ mode := .normal }, {}) } .down (.key (.char 'h'))).2
  == [Effect.emit ⟨.down, .key .left⟩, Effect.emit ⟨.up, .key .left⟩]

/-! ### Crossing the binding, in both directions

A stream that changes which backend owns the keyboard three times.  vi's `State`
and the evaluator's `St` are both live throughout: resetting either on a switch
is what would strand a key. -/

private def mixed : List (Dir × Kanata.Code) :=
  [ (.down, at? 55), (.up, at? 55)                    -- the evaluator: insert
  , (.down, .capsLock), (.up, .capsLock)              -- the mode key: to vi
  , (.down, .key (.char 'd')), (.down, .key (.char 'd'))
  , (.down, .key (.char 'i'))                         -- vi enters insert: back
  , (.down, at? 55), (.up, at? 55) ]

#guard keys (go realBack realW mixed) == "home shift+down del"
#guard codes (go realBack realW mixed) == "down , up , down , up ,"
#guard (go realBack realW mixed).1.backend.1.mode == Mode.insert

/-! ### A release belongs to whoever recorded the press

Caps Lock can move the binding with a finger still down, so the backend bound
when a key comes up is not always the one that saw it go down.  Both directions
of that are here, and both are cases where getting it wrong leaves a key held
in the application. -/

-- Pressed under the evaluator, released under vi: the codes still come back,
-- because vi answers "not mine" for a release it has no record of and the
-- evaluator is asked next.
#guard codes (go realBack realW
    [(.down, at? 54), (.down, .capsLock), (.up, at? 54)])
  == "down lsft up lsft"

-- Pressed under vi in insert mode, released after the mode key: `prelude`'s
-- release guard forwards it, because `State.down` remembers the press.  The
-- down and the up therefore still pair up into one keystroke, with a mode
-- change in the middle of it.
#guard keys (go viBack viInsertW
    [(.down, .key (.char 'h')), (.down, .capsLock), (.up, .key (.char 'h'))])
  == "h"

-- A release nobody recorded emits nothing, which is what all three keepers of a
-- record already do on their own: focus changes and restarts produce these all
-- the time.
#guard codes (go realBack realW [(.up, at? 55)]) == ""
#guard (go realBack realW [(.up, at? 55)]).2 == []

/-! ## The wire

`Bridge.code_roundTrip` is what says the crossing is faithful; this is the
statement at the edge cases that would break it. -/

#guard ofKeyCode? .down 57 == some (Dir.down, Kanata.Code.capsLock)
#guard ofKeyCode? .down 56 == some (Dir.down, Kanata.Code.modifier .shift .left)
#guard ofKeyCode? .down 72 == some (Dir.down, Kanata.Code.extra .volumeUp)
#guard toKeyCode? ⟨.down, .extra .volumeUp⟩ == some (Dir.down, (72 : Quartz.KeyCode))

-- Every code the evaluator can name either has a keycode that names it back, or
-- has none at all.  `Bridge.toKeyCode_injective` is the proof; this is the
-- fixture's own 72 positions, where a silent collision would be worst.
#guard (List.range 72).all fun i =>
  match (at? i).toKeyCode? with
  | some k => ofKeyCode? .down k == some (Dir.down, at? i)
  | none => true

end CapslockMode.Tests.Dispatch
