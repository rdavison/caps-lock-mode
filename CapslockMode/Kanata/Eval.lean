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
    .ok ({ base := a.switch.getD st.base, holds := (i, a) :: st.holds },
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

/-- Fold a stream of events. -/
def run (cfg : Cfg n) (st : St) (evs : List (Dir × Fin n)) :
    Except String (St × List Event) :=
  evs.foldlM (init := (st, ([] : List Event))) fun acc dp =>
    match dp.1 with
    | .down => do
      let (s, o) ← press cfg acc.1 dp.2
      .ok (s, acc.2 ++ o)
    | .up =>
      let (s, o) := release acc.1 dp.2
      .ok (s, acc.2 ++ o)

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
