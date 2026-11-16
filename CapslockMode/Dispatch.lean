/-
# Modes bound to backends

`insert` stops being a branch inside `step` and becomes a *binding*: a mode
bound to a backend, which may be the vi machine or a kanata evaluator running a
particular config.  `step` is not modified at all -- it *is* the vi backend now,
and everything here sits above it.

That is the whole reason the result at the bottom of this file can be a
corollary of `Kanata.resolve_identity` instead of a promise the machine
hardcodes: transparency is what the identity config *does*, and the dispatcher
only has to not get in its way.

## A backend is a parameter, not a constructor

`dispatch` never names a backend.  A backend is a coalgebra -- its own state
type, its own unfold -- supplied as an argument, and vi and kanata are two
*instances* of that rather than two arms of an enum the dispatcher case-splits
on.  Adding a third backend therefore means writing one more `Step`, not editing
this module's core types.

The project's rule about `DecidableEq` is what makes this worth stating.
`Platform.lean` says an enumeration is used "so that `Config` stays decidable
and `Repr`-able", and that is true of a function stored *in* a structure.  A
function **passed to** one costs nothing: `World σ` derives all three instances
given them for `σ`, and `Step σ` never appears in a field.  So the comonadic
reading -- a backend evaluates in a context -- can be taken literally here.

Note what that removed.  The `Option (Sigma fun n => Kanata.Cfg n)` this design
was sketched with existed only because a `Cfg n` had to sit in a decidable
*field*; as a parameter the width is an ordinary implicit, and the existential
goes away with it.

## Why the split sits above `step` and not inside it

`Kanata.Code` is a physical position; `PhysKey` is a key *above* the layout, as
`Key.char`'s own documentation says ("the driver has already applied Shift").
kanata belongs below the layout and vi above it, so a `Code ↔ PhysKey`
conversion in the middle of the machine would be lossy in the one direction that
matters: `Code.toPhys?` has no image for `🔅 🔆 ◀◀ ▶⏸ ▶▶ 🔇 🔉 🔊`, and the real
config's `deflayer` F-rows are entirely those.  Splitting *above* `step` keeps
the kanata branch in `Code` space, where nothing is dropped, and pays the
conversion only on the vi branch -- which has to pay it anyway, because that is
what vi is.

## Where the mode lives, and why nothing can drift

There is no tag saying which backend is live.  `select` re-derives it from the
state on every edge, so the question "does the cached tag still agree with the
mode?" cannot be asked: the binding is a *function* of `State.mode`, applied in
one place, and duplicating it into a field is what would have created the hazard
rather than what would have exposed it.

What the shape does create is one real obligation, and it is the dispatcher's
own: a position no backend claims is passed through, and a pass-through has to
be matched on release or an application is left believing a key is held.
`World.through` is that record and `up_only_if_through` is that promise --
`State.down` for `prelude`, `St.holds` for the evaluator, `through` for the
layer that has no backend to be accountable to.
-/
import CapslockMode.Invariants
import CapslockMode.Kanata
import CapslockMode.Bridge

namespace CapslockMode.Dispatch

/-! ## The vocabulary -/

/-- What a backend did, defunctionalised.

A **list** of effects and not a continuation tree: `Free f a` with `f` a real
functor needs function fields, and `Config`, `State` and `Mode` all derive
`DecidableEq, Repr, Inhabited`.  The structure is still the monadic one; this is
its first-order presentation, which is the one that keeps the proofs.

`emit` and `emitCode` are two channels rather than one because the backends
genuinely answer in different vocabularies: vi synthesises `Chord`s above the
layout, an evaluator resolves positions below it.  Collapsing them would mean
converting a `Code` to a `PhysKey` here, which is the lossy direction this whole
design exists to avoid.

`emitText` is separate again for the reason `Kanata.Action.text` is separate
from `Action.keys`: a `unicode` character has no release to give back, so it is
not a key going down.  `Kanata.press` deliberately does not emit it and leaves
it on the resolved action for a caller that can type text, so a dispatcher that
did not carry it would drop it silently. -/
inductive Effect where
  /-- A key a backend synthesised, above the layout. -/
  | emit (e : OutputEvent)
  /-- A position a backend resolved to, or one nobody rewrote. -/
  | emitCode (e : Kanata.Event)
  /-- Characters typed outright, from `unicode`. -/
  | emitText (cs : List Char)
  /-- The mode moved.  It carries no backend, and that is the point rather than
  an omission: which backend owns the keyboard is a function of the mode,
  re-derived on every edge, so naming the mode already names the backend.
  Carrying a tag alongside is exactly the duplication that would need an
  invariant to keep honest. -/
  | enter (m : Mode)
  /-- kanata's `layer-switch`: a new base layer that outlives the release.  A vi
  mode change and this are two entries in one list now, which is what
  decoupling modes from backends buys. -/
  | setBase (layer : Nat)
  /-- A form a backend recognised and refuses, and why.  Carrying the form as
  well as the reason is the difference between "not supported yet" and a
  message; `Kanata.Blocked` keeps the two apart for the same reason. -/
  | refused (form : String) (why : Kanata.Reason)
  deriving DecidableEq, Repr, Inhabited

namespace Effect

/-- The `OutputEvent`s in a run, which is what every theorem in
`CapslockMode.Invariants` is about. -/
def emitted : List Effect → List OutputEvent
  | [] => []
  | .emit e :: es => e :: emitted es
  | _ :: es => emitted es

/-- The positions in a run, which is what a driver on the Quartz wire posts
through `Kanata.Code.toKeyCode?`. -/
def codes : List Effect → List Kanata.Event
  | [] => []
  | .emitCode e :: es => e :: codes es
  | _ :: es => codes es

@[simp] theorem emitted_map_emit (l : List OutputEvent) : emitted (l.map Effect.emit) = l := by
  induction l with
  | nil => rfl
  | cons e l ih => simp [emitted, ih]

@[simp] theorem codes_map_emitCode (l : List Kanata.Event) :
    codes (l.map Effect.emitCode) = l := by
  induction l with
  | nil => rfl
  | cons e l ih => simp [codes, ih]

@[simp] theorem emitted_map_emitCode (l : List Kanata.Event) :
    emitted (l.map Effect.emitCode) = [] := by
  induction l with
  | nil => rfl
  | cons e l ih => simp [emitted, ih]

@[simp] theorem emitted_map_refused (l : List String) (r : String → Kanata.Reason) :
    emitted (l.map fun f => Effect.refused f (r f)) = [] := by
  induction l with
  | nil => rfl
  | cons f l ih => simp [emitted, ih]

@[simp] theorem emitted_append (a b : List Effect) :
    emitted (a ++ b) = emitted a ++ emitted b := by
  induction a with
  | nil => rfl
  | cons e a ih => cases e <;> simp [emitted, ih]

end Effect

/-- One edge off the wire: a direction, a physical position, and the modifier
level the dispatcher recovered.

The dispatcher's input vocabulary, in position space, mirroring `InputEvent` in
key space.  `mods` rides along rather than living in a backend's state because a
backend sees only the edges routed to it: one that was not bound when Shift went
down could never learn that Shift is held, and `Quartz.applyShift` is the line
where that would show up as `D` quietly becoming `d`. -/
structure Edge where
  dir : Dir
  code : Kanata.Code
  mods : Mods := {}
  /-- The stamp the wire carried, in position space.

  `Edge` mirrors `InputEvent`, and this is the one field that genuinely has to
  be in both: a backend below the layout decides a tap-hold by it, and the guard
  above the layout decides the mode key by it, and neither can read the other's
  vocabulary.  Defaulted for the same reason `InputEvent.time` is -- an
  unstamped wire is one on which nothing has ever timed out. -/
  time : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- A backend: a coalgebra on edges.  Its own state, and an unfold from one edge
to a new state and the effects it asks for.

`none` is **"not mine"**, and it has to be part of the type.  A backend with no
name for a position must be able to say so: swallowing it loses a key, and
answering with a pass-through of its own would double up with whatever the next
backend says.  Refusal is also what makes a chain possible, which is what a
release needs -- see `select`.

A parameter and never a field, for the reason in the module header. -/
abbrev Step (σ : Type) := σ → Edge → Option (σ × List Effect)

/-- Everything the dispatcher remembers.  Three fields, and each is the
dispatcher's own rather than a backend's.

`through` is the one worth reading twice.  A position no backend claims is
passed through unchanged, and its release has to be passed through too -- so the
dispatcher keeps the same kind of record `prelude` keeps in `State.down` and the
evaluator keeps in `St.holds`, for the emissions that are nobody else's.
`up_only_if_through` is the resulting promise. -/
structure World (σ : Type) where
  /-- The bound backend's own state. -/
  backend : σ
  /-- Which modifier positions are held, recovered from the edges the wire
  reported.  `Mods` has no side, which is the same collapse `PhysKey.mod` makes
  and all that `applyShift` and a `Chord` ever need. -/
  mods : Mods := {}
  /-- Positions the dispatcher passed through because no backend claimed them. -/
  through : List Kanata.Code := []
  deriving DecidableEq, Repr, Inhabited

/-- The modifier level after this edge.  Only a modifier position moves it: Caps
Lock does not, because it is the mode key and `Mods` has no alpha-shift bit to
move anyway, which is the same reason the supported macOS setup remaps it to
F18. -/
def World.level (w : World σ) (dir : Dir) (c : Kanata.Code) : Mods :=
  match c with
  | .modifier m _ => w.mods.set m dir.isDown
  | _ => w.mods

/-! ## The wire

The dispatcher speaks `Code`, and on macOS the wire speaks virtual keycodes.
`CapslockMode.Bridge` is that translation and it is physical-to-physical, which
is why it can carry a round trip where `Code.toPhys?` cannot. -/

/-- A position arriving off the Quartz wire. -/
def ofKeyCode? (dir : Dir) (code : Quartz.KeyCode) : Option (Dir × Kanata.Code) :=
  (Quartz.codeOf? code).map fun c => (dir, c)

/-- A position going back on to it. -/
def toKeyCode? (e : Kanata.Event) : Option (Dir × Quartz.KeyCode) :=
  e.key.toKeyCode?.map fun k => (e.dir, k)

/-- **The crossing is faithful.**  Whatever comes back in `Code` space names the
position it was given, so nothing is silently rewritten by the translation
itself.  This is `Bridge.code_roundTrip` doing the job it was landed for, one
level up. -/
theorem wire_roundTrip (dir : Dir) (c : Kanata.Code) (k : Quartz.KeyCode)
    (h : c.toKeyCode? = some k) : ofKeyCode? dir k = some (dir, c) := by
  simp [ofKeyCode?, Bridge.code_roundTrip c k h]

/-! ## The dispatcher

Generic in the backend, and it names none.  What is left once the backends are
parameters is exactly three things: recover the modifier level from the edges,
run the coalgebra, and be accountable for the positions it had to pass through
itself. -/

/-- **The dispatcher.**  One physical position in, effects out. -/
def dispatch {σ : Type} (back : Step σ) (w : World σ) (dir : Dir) (c : Kanata.Code)
    (time : Nat := 0) : World σ × List Effect :=
  let mods := w.level dir c
  match back w.backend { dir := dir, code := c, mods := mods, time := time } with
  | some r => ({ w with backend := r.1, mods := mods }, r.2)
  | none =>
    -- Nobody claimed it, so the dispatcher answers -- and then owes the release.
    match dir with
    | .down =>
      ({ w with mods := mods
                through := if w.through.contains c then w.through else c :: w.through },
        [.emitCode ⟨.down, c⟩])
    | .up =>
      if w.through.contains c then
        ({ w with mods := mods, through := w.through.filter (· != c) }, [.emitCode ⟨.up, c⟩])
      else ({ w with mods := mods }, [])

/-- Feed a stream of positions through the dispatcher, in the shape of
`Machine.run`. -/
def run {σ : Type} (back : Step σ) (w : World σ) :
    List (Dir × Kanata.Code) → World σ × List Effect
  | [] => (w, [])
  | (dir, c) :: rest =>
    let r := dispatch back w dir c
    let s := run back r.1 rest
    (s.1, r.2 ++ s.2)

/-- `run`, with a millisecond stamp on each position.

`run` is the all-zero case, which is why it keeps its meaning rather than
quietly becoming a lie: an unstamped stream is one on which nothing ever times
out, so every tap-hold on it resolves as a tap. -/
def runAt {σ : Type} (back : Step σ) (w : World σ) :
    List (Dir × Kanata.Code × Nat) → World σ × List Effect
  | [] => (w, [])
  | (dir, c, t) :: rest =>
    let r := dispatch back w dir c t
    let s := runAt back r.1 rest
    (s.1, r.2 ++ s.2)

/-- A claimed edge is the backend's answer and nothing else: the dispatcher adds
no effects of its own on top of one.  Trivial, and worth stating -- it is what
says this layer is a router and not a second machine. -/
theorem dispatch_of_claimed {σ : Type} (back : Step σ) (w : World σ) (dir : Dir)
    (c : Kanata.Code) (s : σ) (eff : List Effect)
    (hb : back w.backend { dir := dir, code := c, mods := w.level dir c } = some (s, eff)) :
    dispatch back w dir c = ({ w with backend := s, mods := w.level dir c }, eff) := by
  simp [dispatch, hb]

/-- **No stray pass-throughs.**  The dispatcher emits a key-up of its own only
for a position whose key-down it emitted.

This is `Invariants.up_only_if_pressed` at the dispatcher's own layer, and it is
the obligation this shape creates: `prelude` is accountable for what it forwards
and a backend for what it claims, so the passed-through remainder needs a
keeper. -/
theorem up_only_if_through {σ : Type} (back : Step σ) (w : World σ) (c : Kanata.Code)
    (hb : back w.backend { dir := .up, code := c, mods := w.level .up c } = none)
    (hn : c ∉ w.through) : (dispatch back w .up c).2 = [] := by
  simp [dispatch, hb, hn]

/-- ... and the other half: a pass-through is remembered, so its release will be
passed through too, whatever happens to the binding in between. -/
theorem down_through_remembered {σ : Type} (back : Step σ) (w : World σ) (c : Kanata.Code)
    (hb : back w.backend { dir := .down, code := c, mods := w.level .down c } = none) :
    c ∈ (dispatch back w .down c).1.through := by
  simp only [dispatch, hb]
  split
  · next h => simpa using h
  · simp

/-! ## Combinators over backends

Still generic: nothing below names vi or kanata either, except where a doc
comment explains what a shape is *for*. -/

/-- The backend that answers nothing at all.  The unit of `select`, and what a
one-backend assembly pairs with. -/
def nothing : Step Unit := fun _ _ => none

/-- Two backends, both live, with a parameter choosing which one owns the
keyboard.

**Both states persist.**  Discarding the unselected one on a switch would
strand exactly the keys that were down when it happened:
`Machine.down_remembered` says a forwarded press will have its release
forwarded, and `Kanata.release_undoes_press` says a held position gives its
codes back, and neither promise survives its state being reset underneath it.

**The unselected backend is asked, not asleep.**  A backend that answers `none`
falls through to the other, which is what makes a position pressed under one
binding releasable under the other -- the mode key can move the binding with a
finger still down, and a release belongs to whoever recorded the press rather
than to whoever is bound now.

`first` is a function of the two states and is evaluated on every edge, so there
is no cached answer to drift from them.  That is the whole of what a
`backend : Backend` field would have needed an invariant to protect. -/
def select {σ₁ σ₂ : Type} (first : σ₁ → σ₂ → Bool) (b₁ : Step σ₁) (b₂ : Step σ₂) :
    Step (σ₁ × σ₂) := fun s e =>
  let ask₁ : Option ((σ₁ × σ₂) × List Effect) := (b₁ s.1 e).map fun r => ((r.1, s.2), r.2)
  let ask₂ : Option ((σ₁ × σ₂) × List Effect) := (b₂ s.2 e).map fun r => ((s.1, r.1), r.2)
  if first s.1 s.2 then ask₁.or ask₂ else ask₂.or ask₁

/-- Which backend answers is decided on this edge, from these states, and by
nothing remembered from an earlier one. -/
theorem select_first {σ₁ σ₂ : Type} (first : σ₁ → σ₂ → Bool) (b₁ : Step σ₁) (b₂ : Step σ₂)
    (s : σ₁ × σ₂) (e : Edge) (t : σ₁) (eff : List Effect)
    (hf : first s.1 s.2 = true) (h : b₁ s.1 e = some (t, eff)) :
    select first b₁ b₂ s e = some ((t, s.2), eff) := by
  simp [select, hf, h]

/-- The mirror of `select_first`. -/
theorem select_second {σ₁ σ₂ : Type} (first : σ₁ → σ₂ → Bool) (b₁ : Step σ₁) (b₂ : Step σ₂)
    (s : σ₁ × σ₂) (e : Edge) (t : σ₂) (eff : List Effect)
    (hf : first s.1 s.2 = false) (h : b₂ s.2 e = some (t, eff)) :
    select first b₁ b₂ s e = some ((s.1, t), eff) := by
  simp [select, hf, h]

/-- The event a backend above the layout sees for a position, if it can name the
position at all.

`Code.toPhys?` is the right amount of lossy here, and that is not the claim the
bridge makes: the bridge needs injectivity and so cannot collapse left and
right, whereas a `PhysKey` has nowhere to put a side and no constructor for
`🔊`.  So `none` is an answer and not a failure.

`Quartz.applyShift` is applied because `Backend/Quartz.lean` is where this
project puts the layout boundary: a `Code` is the unshifted legend of a position
and `Key.char` is the character the layout produced, so `shift`+`d` has to
arrive as `Key.char 'D'` or every upper-case vi command stops working.

What is deliberately *not* reused is `Quartz.decode`.  Its extra job is
recovering a modifier transition by diffing two levels, which macOS forces on a
client because a tap reports levels rather than edges.  An `Edge` is already an
edge, so calling `decode` would be asking a level-to-edge converter to
rediscover what it was handed. -/
def viEvent? (e : Edge) : Option InputEvent :=
  (Kanata.Code.toPhys? e.code).map fun pk =>
    { dir := e.dir
      key := match pk with
        | .key k => .key (Quartz.applyShift k e.mods.shift)
        | _ => pk
      mods := e.mods
      time := e.time }

/-- Announce a mode change, if there was one.  A named function rather than a
`let` inside `guarded` so that the `enter` is one expression instead of four
copies of the same `if`, and so a proof can unfold it on its own. -/
def announce (before : Mode) (r : (State × σ) × List Effect) : (State × σ) × List Effect :=
  if r.1.1.mode == before then r else (r.1, r.2 ++ [Effect.enter r.1.1.mode])

/-- An announcement is exactly that: it changes neither the state a backend
reached nor the keystrokes it asked for.  The two lemmas every proof below
about a wrapped backend needs, so that none of them has to case-split on
whether the mode moved. -/
@[simp] theorem announce_state (before : Mode) (r : (State × σ) × List Effect) :
    (announce before r).1 = r.1 := by
  unfold announce; split <;> rfl

@[simp] theorem announce_emitted (before : Mode) (r : (State × σ) × List Effect) :
    Effect.emitted (announce before r).2 = Effect.emitted r.2 := by
  unfold announce
  split
  · rfl
  · simp [Effect.emitted]

/-- `prelude`, in front of any backend at all.

This is what the guards were hoisted out of `step` for.  All three are about
being a *keyboard filter* -- an injected event, a release matched against a
record, and the mode key -- and none of them is vi-specific, so they can run in
front of a backend that knows nothing about them.  The mode key especially:
bound inside a kanata config it would be the only way back out, and a `defsrc`
that mentions `caps` will happily rewrite it.

The state is `State × σ`, and that is not this transformer naming vi.  `State`
is where a keyboard filter's own bookkeeping lives -- `down` is the record a
key-up is matched against and `mode` is what the mode key moves -- and
`Machine.prelude` is the statement that this half of `State` is not vi's.

Two details:

* **A key-up the guards decline is not resolved.**  The release guard forwards a
  key-up exactly when it forwarded the key-down, which it knows from `down`.  A
  key-up it has no record of is handed on, because something else may have one.
* **This is also where a mode change is announced.**  It is the one layer that
  sees every edge and holds the `State`, so it can compare the mode before and
  after, and `Effect.enter` needs no help from a backend.  Returning `none`
  discards the guards' own `State`, which is safe because the only paths that
  reach it leave the state untouched: `prelude` moves it exactly when it also
  resolves the event. -/
def guarded {σ : Type} (cfg : Config) (back : Step (State × σ)) : Step (State × σ) :=
  fun s e =>
    match viEvent? e with
    | none => (back s e).map (announce s.1.mode)
    | some iev =>
      match prelude cfg s.1 iev with
      | .handled st' out =>
        if e.dir == .up && out.isEmpty then (back (st', s.2) e).map (announce s.1.mode)
        else some (announce s.1.mode ((st', s.2), out.map Effect.emit))
      | .dispatch st' _ => (back (st', s.2) e).map (announce s.1.mode)

/-! ## The vi backend -/

/-- The vi machine as a backend.

Releases answer `none` rather than silence, and that is deliberate: `prelude`
answers for every key-up it has a record of, so a key-up reaching *here* is one
vi did not forward -- and something else may have.  Saying "not mine" is what
lets a position pressed under one binding be released under another.

A position with no `PhysKey` is `none` too.  vi lives above the layout, and a
position with no key is below its floor. -/
def vi (cfg : Config) : Step State := fun st e =>
  match viEvent? e with
  | none => none
  | some iev =>
    match e.dir with
    | .up => none
    | .down =>
      let r := viStep cfg st iev
      some (r.1, r.2.map Effect.emit)

/-- vi alone, behind the guards.  This is `step` again -- the shape the project
has today, recovered as an assembly rather than written into the machine. -/
def viAlone (cfg : Config) : Step (State × Unit) :=
  guarded cfg (select (fun _ _ => true) (vi cfg) nothing)

/-- `prelude` leaves the state alone when it hands an event on.  Needed twice
below, and not provable by `rfl`: `prelude` has three guards in front of the
answer. -/
theorem prelude_dispatch_eq {cfg : Config} {st st' : State} {ev ev' : InputEvent}
    (h : prelude cfg st ev = .dispatch st' ev') : st' = st ∧ ev' = ev := by
  unfold prelude at h
  split at h
  · simp at h
  · split at h
    · split at h <;> simp at h
    · split at h
      · simp at h
      · exact ⟨(Pre.dispatch.inj h).1.symm, (Pre.dispatch.inj h).2.symm⟩

/-- **Binding vi is binding `step`.**  The state it leaves and the keystrokes it
emits are exactly `step`'s, because `prelude` and then `viStep` is what `step`
is *defined* to be.  There is no second machine here to drift from the proved
one, so `Invariants.lean` is still a list of promises about the backend that is
bound.

The answer is read through `Effect.emitted` rather than compared whole, because
a mode change adds an `enter` that `step` has no vocabulary for; the
`OutputEvent`s are the part of the answer `step` is about. -/
theorem viAlone_down (cfg : Config) (st : State) (e : Edge) (iev : InputEvent)
    (hd : e.dir = .down) (hv : viEvent? e = some iev) :
    (viAlone cfg (st, ()) e).map (fun r => (r.1.1, Effect.emitted r.2))
      = some ((step cfg st iev).1, (step cfg st iev).2) := by
  simp only [viAlone, guarded, hv]
  match hpre : prelude cfg st iev with
  | .handled st' out =>
    rw [step_of_handled hpre, hd]
    simp
  | .dispatch st' ev' =>
    obtain ⟨hst, hev⟩ := prelude_dispatch_eq hpre
    have hstep : step cfg st iev = viStep cfg st iev := by
      unfold step; rw [hpre, hst, hev]
    rw [hstep, hst, hev]
    simp [select, vi, hv, hd]

/-! ## The kanata backend -/

/-- The `defsrc` position a code occupies.

`defsrc` *is* the position table, so this is a lookup and not a conversion. -/
def srcPos? (cfg : Kanata.Cfg n) (c : Kanata.Code) : Option (Fin n) :=
  (cfg.src.toList.findIdx? (· == c)).bind (Kanata.pos? n)

/-- The position really is the one that was asked for.  Needed by the
transparency result, which has to know that the code handed back is the code it
was given and not merely *a* code. -/
theorem srcPos?_eq {cfg : Kanata.Cfg n} {c : Kanata.Code} {p : Fin n}
    (h : srcPos? cfg c = some p) : cfg.src[p.val]'p.isLt = c := by
  unfold srcPos? at h
  match hf : cfg.src.toList.findIdx? (· == c) with
  | none => rw [hf] at h; simp at h
  | some i =>
    rw [hf] at h
    simp only [Option.bind_some] at h
    unfold Kanata.pos? at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      obtain ⟨_, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
      simpa using beq_iff_eq.mp hp
    · simp at h

/-- The evaluator as a backend.

It claims every edge, and the case that looks as though it should not is the
point: a position `defsrc` does not mention is handed back unchanged rather than
declined.  kanata's own rule is that such a key is not intercepted, and
"unchanged" is what not intercepting *means* -- there is no lower layer to ask,
because below the layout the evaluator is the floor.

`Edge.mods` is ignored, and that is not an oversight either.  A modifier is a
position to this evaluator and not a level: its own `St.holds` is where the
level lives, which is exactly why it sits below the layout and vi does not.

A press that resolves to a refused form emits nothing and says so.  Silence is
the failure that hides -- the same reason `Cfg.blocked` exists at all, and the
same reason `Main.runQuartz` prints a `dropLine` for an event that decodes to
nothing. -/
def kanata (cfg : Kanata.Cfg n) : Step Kanata.St := fun st e =>
  match srcPos? cfg e.code with
  | none => some (st, [.emitCode ⟨e.dir, e.code⟩])
  | some p =>
    match e.dir with
    | .up =>
      let r := Kanata.release st p
      some (r.1, r.2.map Effect.emitCode)
    | .down =>
      -- `press` is `pressAction` applied to `resolve`, so this is that same
      -- resolution and not a second one; it is spelled out because the layer
      -- switch, the refused forms and the typed text are all on the action
      -- rather than in the events.
      let a := Kanata.resolve cfg st p
      match Kanata.press cfg st p with
      | .ok (st', evs) =>
        some (st',
          evs.map Effect.emitCode
            ++ (if a.text.isEmpty then [] else [Effect.emitText a.text])
            ++ (match a.switch with | some i => [Effect.setBase i] | none => []))
      | .error _ => some (st, a.blocked.map fun f => Effect.refused f (Kanata.reasonOf f))

/-! ## The assembly

The only place that names a backend.  Everything above is generic in exactly the
way a third one would need it to be. -/

/-- The modes bound to the evaluator; every other mode is vi's.

A list of modes and not a `Mode → Backend` function, because this one *is* a
field of a configuration and `DecidableEq` has to survive it -- the constraint
bites here and not on `Step`.  Empty is today's behaviour exactly, every mode
vi's, which is what makes this module additive rather than a replacement. -/
abbrev Bound := List Mode

/-- vi and a kanata config, both live, bound by mode, behind the guards. -/
def modal (cfg : Config) (bound : Bound) (kcfg : Kanata.Cfg n) : Step (State × Kanata.St) :=
  guarded cfg (select (fun st _ => !bound.contains st.mode) (vi cfg) (kanata kcfg))

/-- A mode in `bound` sends its edges to the evaluator, decided from the state
on this edge.  This is all that is left of the agreement invariant the sketched
shape needed: there is nothing to agree *with*. -/
theorem modal_bound (cfg : Config) (bound : Bound) (kcfg : Kanata.Cfg n) (st : State)
    (kan : Kanata.St) (e : Edge) (t : Kanata.St) (eff : List Effect)
    (hm : st.mode ∈ bound) (hv : viEvent? e = none)
    (h : kanata kcfg kan e = some (t, eff)) :
    modal cfg bound kcfg (st, kan) e = some ((st, t), eff) := by
  have hf : (!bound.contains st.mode) = false := by simp [hm]
  have hsel := select_second (fun (s : State) (_ : Kanata.St) => !bound.contains s.mode)
    (vi cfg) (kanata kcfg) (st, kan) e t eff hf h
  simp only [modal, guarded, hv]
  rw [hsel]
  simp [announce]

/-! ## Transparency, re-derived

The payoff.  `Invariants.run_insert_transparent` says the machine passes your
keystrokes through while it is switched off, and says it about a branch written
into `step`.  Here the same property is obtained one level up from
`Kanata.resolve_identity`: it is what the identity config *does*, and the
dispatcher inherits it. -/

/-- The assembly the payoff is about: `insert` is not a branch any more, it is a
binding -- to the evaluator, running one layer of all `_` over the positions the
keyboard actually has. -/
def identity (src : Vector Kanata.Code n) : Step (State × Kanata.St) :=
  modal {} [.insert] (Kanata.Cfg.identity src)

/-- **The identity config emits the position it was given**, whatever state the
evaluator is in and wherever in `defsrc` the position sits -- or whether it sits
there at all.

`Kanata.resolve_identity_any` is doing all of the work.  The backend's
contribution is the `defsrc` lookup, and that is exactly the point: transparency
is a property of the config, not an arrangement made here. -/
theorem kanata_identity (src : Vector Kanata.Code n) (st : Kanata.St) (e : Edge)
    (hd : e.dir = .down) :
    ∃ st', kanata (Kanata.Cfg.identity src) st e
      = some (st', [Effect.emitCode ⟨.down, e.code⟩]) := by
  unfold kanata
  match hp : srcPos? (Kanata.Cfg.identity src) e.code with
  | none => exact ⟨st, by simp [hd]⟩
  | some p =>
    have hc := srcPos?_eq hp
    simp only [Kanata.Cfg.identity] at hc
    refine ⟨{ base := st.base, holds := (p.val, { keys := [e.code] }) :: st.holds }, ?_⟩
    simp [hd, Kanata.press, Kanata.pressAction, Kanata.resolve_identity_any, hc]

/-- `prelude` lets a press past when it is not the mode key: the other side of
`Invariants.prelude_toggle_down`, and the half a dispatcher needs, since its
question is when it *may* consult the bound backend. -/
theorem prelude_dispatch (cfg : Config) (st : State) (ev : InputEvent)
    (hd : ev.dir = .down) (hi : ev.injected = false) (ht : ev.key ≠ cfg.toggleKey) :
    prelude cfg st ev = .dispatch st ev := by
  rw [prelude, if_neg (by simp [hi]), hd]
  simp [ht]

/-- What `viEvent?` guarantees about the event it builds.  Trivial, and needed
because `prelude` asks about `dir` and `injected` before it will let anything
past. -/
theorem viEvent_dir {e : Edge} {iev : InputEvent} (h : viEvent? e = some iev) :
    iev.dir = e.dir ∧ iev.injected = false := by
  unfold viEvent? at h
  match hp : Kanata.Code.toPhys? e.code with
  | none => rw [hp] at h; simp at h
  | some pk =>
    rw [hp] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩

/-- A position vi would call Caps Lock is Caps Lock.  `Code.toPhys?` is lossy,
but not on the one value the mode key is. -/
theorem toPhys_capsLock {c : Kanata.Code} (h : Kanata.Code.toPhys? c = some .capsLock) :
    c = .capsLock := by
  cases c with
  | key k => simp [Kanata.Code.toPhys?] at h
  | modifier m s => simp [Kanata.Code.toPhys?] at h
  | capsLock => rfl
  | extra e => simp [Kanata.Code.toPhys?] at h

/-- ... and therefore no other position decodes to Caps Lock.  `applyShift`
cannot conjure one either: it only ever rewrites a `char`. -/
theorem viEvent_key_ne {e : Edge} {iev : InputEvent} (hc : e.code ≠ .capsLock)
    (h : viEvent? e = some iev) : iev.key ≠ .capsLock := by
  intro hk
  unfold viEvent? at h
  match hp : Kanata.Code.toPhys? e.code with
  | none => rw [hp] at h; simp at h
  | some pk =>
    rw [hp] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    cases pk with
    | key k => simp at hk
    | mod m => simp at hk
    | capsLock => exact hc (toPhys_capsLock hp)

/-- One press, with the identity config bound to the mode the machine is in.
The vi `State` comes back untouched, which is what keeps the binding where it
was without anything having to check. -/
theorem identity_press (src : Vector Kanata.Code n) (st : State) (kan : Kanata.St) (e : Edge)
    (hm : st.mode = .insert) (hd : e.dir = .down) (hc : e.code ≠ .capsLock) :
    ∃ kan', identity src (st, kan) e
      = some ((st, kan'), [Effect.emitCode ⟨.down, e.code⟩]) := by
  obtain ⟨kan', hk⟩ := kanata_identity src kan e hd
  refine ⟨kan', ?_⟩
  have hf : (!([Mode.insert] : Bound).contains st.mode) = false := by simp [hm]
  have hsel := select_second
    (fun (s : State) (_ : Kanata.St) => !([Mode.insert] : Bound).contains s.mode)
    (vi ({} : Config)) (kanata (Kanata.Cfg.identity src)) (st, kan) e kan' _ hf hk
  simp only [identity, modal, guarded]
  match hv : viEvent? e with
  | none =>
    rw [hsel]
    simp [announce]
  | some iev =>
    obtain ⟨hdir, hinj⟩ := viEvent_dir hv
    simp only [prelude_dispatch ({} : Config) st iev (hdir.trans hd) hinj (viEvent_key_ne hc hv)]
    rw [hsel]
    simp [announce]

/-- **Transparency, one level up.**  With the identity config bound to `insert`,
the dispatcher emits exactly the position it was given: no rewriting, no extra
events, and nothing but `emitCode`.

Caps Lock is the one exclusion, and it is the same one `run_insert_transparent`
makes with its own `htoggle` hypothesis: the mode key is the position that is
never transparent, because it is how you get out.  Note what is *not* here --
no `hesc`, because `escapeToNormal` is a vi affordance and a mode bound to the
evaluator does not have it, and no hypothesis relating a backend tag to the
mode, because there is no tag. -/
theorem dispatch_identity_transparent (src : Vector Kanata.Code n)
    (w : World (State × Kanata.St)) (c : Kanata.Code)
    (hm : w.backend.1.mode = .insert) (hc : c ≠ .capsLock) :
    (dispatch (identity src) w .down c).2 = [Effect.emitCode ⟨.down, c⟩] := by
  obtain ⟨kan', hk⟩ := identity_press src w.backend.1 w.backend.2
    { dir := .down, code := c, mods := w.level .down c } hm rfl hc
  rw [dispatch_of_claimed _ _ _ _ _ _ hk]

/-- The vi machine is untouched, which is what lets the stream form below
induct: the mode stays where it was, so the binding stays where it was. -/
theorem dispatch_identity_vi (src : Vector Kanata.Code n) (w : World (State × Kanata.St))
    (c : Kanata.Code) (hm : w.backend.1.mode = .insert) (hc : c ≠ .capsLock) :
    (dispatch (identity src) w .down c).1.backend.1 = w.backend.1 := by
  obtain ⟨kan', hk⟩ := identity_press src w.backend.1 w.backend.2
    { dir := .down, code := c, mods := w.level .down c } hm rfl hc
  rw [dispatch_of_claimed _ _ _ _ _ _ hk]

/-- **... and therefore a whole stream is passed through unchanged**, which is
`run_insert_transparent`'s statement re-derived from the evaluator rather than
from a branch in `step`.  Presses only, exactly as `run_insert_transparent`
requires: a release is not the identity on anything, it is the *undoing* of the
press that `Kanata.release_undoes_press` is about. -/
theorem run_identity_transparent (src : Vector Kanata.Code n) (w : World (State × Kanata.St))
    (cs : List Kanata.Code) (hm : w.backend.1.mode = .insert)
    (hc : ∀ c ∈ cs, c ≠ .capsLock) :
    (run (identity src) w (cs.map fun c => (Dir.down, c))).2
      = cs.map fun c => Effect.emitCode ⟨.down, c⟩ := by
  induction cs generalizing w with
  | nil => rfl
  | cons c cs ih =>
    have hvi := dispatch_identity_vi src w c hm (hc c (by simp))
    have hm' : (dispatch (identity src) w .down c).1.backend.1.mode = .insert := by
      rw [hvi]; exact hm
    simp only [List.map_cons, run,
      dispatch_identity_transparent src w c hm (hc c (by simp)),
      ih _ hm' fun c' h => hc c' (by simp [h])]
    simp

end CapslockMode.Dispatch
