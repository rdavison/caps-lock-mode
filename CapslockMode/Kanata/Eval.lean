/-
# Pressing and releasing

A press resolves the position against the current stack, emits its codes in
order, records the action, and applies any `layer-switch`.  A release looks up
the *recorded* action -- never a fresh resolution -- and gives its codes back in
reverse.

Two decisions worth naming, because both could plausibly have gone the other
way:

* **A release of a position that was never pressed emits nothing and is not an
  error.**  A real keyboard does this all the time: focus changes, a driver
  restarts, the machine starts mid-chord.  Treating it as a failure would be
  strict about the wrong thing.
* **`release` does not take the config.**  It cannot need it: the whole point of
  recording the action at press time is that the answer no longer depends on
  anything that could have moved since.  An unused `Cfg` argument would suggest
  otherwise.

`press` is the only half that can fail, and it fails for exactly one reason: the
position resolves to a form this evaluator refuses (`tap-hold`, `one-shot`,
`macro`, `lrld`).  That is a named refusal rather than a silently wrong
keystroke, which is the whole reason `Cfg.blocked` exists.
-/
import CapslockMode.Kanata.Layer

namespace CapslockMode.Kanata

/-- A code going down or coming up.  Distinct from `CapslockMode.OutputEvent`
because a `Code` is not a `PhysKey` -- see the header of `Kanata/Keys.lean`. -/
structure Event where
  dir : Dir
  key : Code
  deriving DecidableEq, Repr, Inhabited

/-- `"down lsft"`, in the same shape as `Protocol.OutputEvent.line`.  Spelled
out here rather than imported: `Protocol` pulls in the whole machine, and these
modules import nothing but `CapslockMode.Key`. -/
def Event.line (e : Event) : String :=
  (match e.dir with | .down => "down " | .up => "up ") ++ e.key.name

/-- What a guard reads: `"down lsft down ; up ; up lsft"`. -/
def render (es : List Event) : String :=
  String.intercalate " " (es.map Event.line)

/-- What a press does once the action is known.  Split out from `press` so that
the config, the bound on the position and the layer walk are all behind it: the
only thing this half can look at is the action, which is exactly what `release`
will later have to work from. -/
def pressAction (st : St) (i : Nat) (a : Action) : Except String (St × List Event) :=
  if a.blocked.isEmpty then
    -- `{ st with ... }` and not a fresh record: a press must not silently clear
    -- a tap-hold decision that is still open.
    .ok ({ st with base := a.switch.getD st.base, holds := (i, a) :: st.holds },
         a.keys.map (Event.mk .down))
  else
    .error s!"position {i} resolves to {String.intercalate ", " a.blocked}, \
which this evaluator does not model"

/-- Press a position. -/
def press (cfg : Cfg n) (st : St) (p : Fin n) : Except String (St × List Event) :=
  pressAction st p.val (resolve cfg st p)

/-- Release a position, undoing whatever its press did. -/
def release (st : St) (p : Fin n) : St × List Event :=
  match st.holds.find? (fun h => h.1 == p.val) with
  | none => (st, [])
  | some ha =>
    ({ st with holds := st.holds.eraseP (fun h => h.1 == p.val) },
     ha.2.keys.reverse.map (Event.mk .up))

/-! ## Tap-hold, and how a pure evaluator hears a timeout

A tap-hold press cannot emit: the decision is not known yet.  So it records a
`Pending` and emits nothing, and the decision is made **retroactively**, by the
next event to arrive -- which is the one thing that carries a clock.

That is enough, and it is worth saying why it is enough rather than a
compromise.  A hold is only ever *observable* through another key: holding a
Ctrl key and pressing nothing should do nothing, because Ctrl alone types
nothing.  So resolving late is indistinguishable from resolving on time, and no
synthetic tick is needed.  What it does not buy is a modifier observably down
*before* the next keystroke -- Ctrl-click, and a UI that highlights live
modifiers.  That is a different feature, and `settle` is the function a tick
channel would call when it is wanted.

**A divergence from kanata, deliberately.**  kanata's plain `tap-hold` does not
resolve on an interrupting press -- that is what `tap-hold-press` adds; plain
`tap-hold` buffers until its timer fires, and buffering needs a timer to flush
it.  So `(tap-hold ...)` here means kanata's **`tap-hold-press` decision rule**.
It is what a caps-as-Ctrl binding needs (holding caps and hitting `c` inside the
window must be Ctrl+C, not a backtick and then a `c`), it needs no buffer, and
it is what every other caps-as-Ctrl setup does.  The eleven other spellings stay
in `clockForms`, so this cannot be read as a claim to model `tap-hold-press`
itself. -/

/-- Settle a pending tap-hold as a hold.

Literally `pressAction` applied to the hold branch, which is what makes the rest
free: the hold's codes land in `holds` under the tap-hold's own position, so its
eventual release gives them back by the route every other press uses, and a
`layer-switch` written in a hold branch lands exactly where one anywhere else
would. -/
def settleHold (st : St) : St × List Event :=
  match st.pending with
  | none => (st, [])
  | some p =>
    let st := { st with pending := none }
    match pressAction st p.pos { toSimple := p.th.hold } with
    -- The second `pending := none` is redundant -- `pressAction` is given a
    -- state that already has none and only writes `base` and `holds` -- and it
    -- is written anyway, so that "a settled hold leaves no decision open" is a
    -- syntactic fact rather than one a reader has to chase through two
    -- definitions.
    | .ok r => ({ r.1 with pending := none }, r.2)
    | .error _ => (st, [])

/-- Settle whatever this edge decides, before the edge's own work.

A press of *another* position decides a pending tap-hold as a hold.  A release
decides nothing here, because the only release that can decide one is the
tap-hold's own, and `releaseAt` answers that with the clock in hand.

Note what is not in the signature: a time.  The interrupt rule is timeless -- an
arriving press resolves the hold whatever the elapsed time -- so the clock is
read in exactly one place in this module, which is `releaseAt`. -/
def settle (st : St) (dir : Dir) (i : Nat) : St × List Event :=
  match st.pending with
  | some p => if dir == .down && p.pos != i then settleHold st else (st, [])
  | none => (st, [])

/-- A settled hold leaves no decision open. -/
theorem settleHold_pending (st : St) : (settleHold st).1.pending = none := by
  rcases hp : st.pending with _ | p
  · simp [settleHold, hp]
  · simp only [settleHold, hp]
    split <;> simp

/-- With nothing pending there is nothing to settle. -/
theorem settle_of_none (st : St) (dir : Dir) (i : Nat) (h : st.pending = none) :
    settle st dir i = (st, []) := by simp [settle, h]

/-- **Settling twice is settling once.**  Stated because `Dispatch.kanata` lifts
the settle out -- it has to, so that the arriving key resolves against a layer
stack the hold may just have pushed -- and `pressAt` then calls it again. -/
theorem settle_idem (st : St) (dir : Dir) (i : Nat) :
    settle (settle st dir i).1 dir i = ((settle st dir i).1, []) := by
  match hp : st.pending with
  | none =>
    rw [settle_of_none st dir i hp]
    exact settle_of_none st dir i hp
  | some p =>
    by_cases h : dir == .down && p.pos != i
    · have hs : settle st dir i = settleHold st := by simp [settle, hp, h]
      rw [hs]
      exact settle_of_none _ dir i (settleHold_pending st)
    · have hs : settle st dir i = (st, []) := by simp [settle, hp, h]
      rw [hs]
      exact hs

/-- Press a position at a time.

A tap-hold press is the one press in this evaluator that says nothing at all:
it records the decision and emits nothing, and the next event decides it. -/
def pressAt (cfg : Cfg n) (st : St) (p : Fin n) (now : Nat) :
    Except String (St × List Event) :=
  let (st, pre) := settle st .down p.val
  match (resolve cfg st p).tapHold with
  | some th =>
    .ok ({ st with pending := some { pos := p.val, th := th, pressedAt := now } }, pre)
  | none => (press cfg st p).map fun r => (r.1, pre ++ r.2)

/-- Release a position at a time.

The one place in this module that reads the clock.  A release of the pending
position decides it; a release of anything else is the release it always was --
including the release of a tap-hold that an interrupting press already settled,
which by then is an ordinary entry in `holds`.

A tap and a hold are both emitted as a press and a release in one step.  For a
tap that is obviously right.  For a hold it is right too: without a timer the
hold was never activated, so activating and deactivating it is the closest
faithful answer, and it is the one that still lands a `layer-switch` written in
a hold branch.  Where the hold is a bare `layer-while-held`, `keys` is empty and
this emits nothing -- which is what kanata is observably doing as well. -/
def releaseAt (st : St) (p : Fin n) (now : Nat) : St × List Event :=
  match st.pending with
  | some pd =>
    if pd.pos == p.val then
      let branch : Simple :=
        if now - pd.pressedAt < pd.th.tapTimeout then pd.th.tap else pd.th.hold
      let st := { st with pending := none }
      match pressAction st p.val { toSimple := branch } with
      | .ok (st', evs) => let r := release st' p; (r.1, evs ++ r.2)
      | .error _ => (st, [])
    else release st p
  | none => release st p

/-- `run`, with a millisecond stamp on each event.

`run` is the all-zero case, which keeps its meaning rather than becoming a lie:
an unstamped stream is one on which nothing ever times out, so every tap-hold on
it resolves as a tap. -/
def runAt (cfg : Cfg n) (st : St) (evs : List (Dir × Fin n × Nat)) :
    Except String (St × List Event) :=
  evs.foldlM (init := (st, ([] : List Event))) fun acc dp =>
    match dp.1 with
    | .down => do
      let (s, o) ← pressAt cfg acc.1 dp.2.1 dp.2.2
      .ok (s, acc.2 ++ o)
    | .up =>
      let (s, o) := releaseAt acc.1 dp.2.1 dp.2.2
      .ok (s, acc.2 ++ o)

/-- `runAt` over positions given as plain numbers, so a test can write what it
means. -/
def runIxAt (cfg : Cfg n) (st : St) (evs : List (Dir × Nat × Nat)) :
    Except String (St × List Event) := do
  let ps ← evs.mapM fun dp =>
    match pos? n dp.2.1 with
    | some p => .ok (dp.1, p, dp.2.2)
    | none => .error s!"position {dp.2.1} is out of range for a {n}-wide config"
  runAt cfg st ps

/-- Fold a stream of events, with no clock.

The all-zero case of `runAt` below rather than a separate fold over `press` and
`release`, so that "an unstamped stream is one on which nothing ever times out"
is true of this function and not just a thing said about it: every tap-hold on
such a stream is released at elapsed `0`, which is inside any timeout, so every
one of them is a tap. -/
def run (cfg : Cfg n) (st : St) (evs : List (Dir × Fin n)) :
    Except String (St × List Event) :=
  runAt cfg st (evs.map fun dp => (dp.1, dp.2, 0))

/-- `run` over positions given as plain numbers, so a test can write what it
means.  An out-of-range position is an error rather than a silent skip. -/
def runIx (cfg : Cfg n) (st : St) (evs : List (Dir × Nat)) :
    Except String (St × List Event) := do
  let ps ← evs.mapM fun dp =>
    match pos? n dp.2 with
    | some p => .ok (dp.1, p)
    | none => .error s!"position {dp.2} is out of range for a {n}-wide config"
  run cfg st ps

/-! ## Press and release cancel -/

/-- Pressing a position and then releasing it restores the state exactly,
provided the action had no `layer-switch` -- a switch is *supposed* to outlive
the release, which is the whole difference between `layer-switch` and
`layer-while-held`.

This is the local analogue of `Machine.step_balanced`: it is what says that
holding a layer key and letting go cannot strand you on the wrong layer. -/
theorem release_undoes_press (cfg : Cfg n) (st : St) (p : Fin n)
    (st' : St) (out : List Event)
    (hsw : (resolve cfg st p).switch = none)
    (h : press cfg st p = .ok (st', out)) :
    release st' p = (st, out.reverse.map (fun e => { e with dir := .up })) := by
  unfold press pressAction at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hst, hout⟩ := h
    subst hst
    subst hout
    simp [release, hsw, List.map_reverse]
  · simp at h

/-- The release also empties `holds` back to what it was, stated on its own
because that is the field a stuck key lives in. -/
theorem release_restores_holds (cfg : Cfg n) (st : St) (p : Fin n)
    (st' : St) (out : List Event)
    (h : press cfg st p = .ok (st', out)) :
    (release st' p).1.holds = st.holds := by
  unfold press pressAction at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hst, _⟩ := h
    subst hst
    simp [release]
  · simp at h

end CapslockMode.Kanata
