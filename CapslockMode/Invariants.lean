/-
# What CapslockMode promises

A keyboard layer is a bad place for surprises: it sits between you and
everything else you use, it runs all day, and when it misbehaves you cannot
even type the command to kill it.  The properties below are the ones that make
it safe to leave switched on.

* `step_balanced` — every synthetic event stream is balanced: no key is ever
  left held, and no key is ever released that was not held.
* `run_insert_transparent` — while CapslockMode is off, it is *exactly* the
  identity on your keystrokes.
* `capsLock_twice` / `esc_resets` — two known ways back to a known state, from
  any state, that emit nothing at all.
* `step_count_le` / `step_repeats_le` — a typo like `99999dd` cannot turn into
  a storm of synthetic keystrokes.
* `operator_progress` / `textObj_progress` — a half-typed command always
  resolves; the machine never quietly swallows your keyboard.
-/
import CapslockMode.Balance
import CapslockMode.Machine

namespace CapslockMode

/-! ## No stuck keys -/

theorem Response.emit_balanced (r : Response) : Balanced r.emit :=
  emitChords_balanced _

/-- **The main safety theorem.**  Whatever state CapslockMode is in, whatever
command key arrives, everything it synthesises is balanced: modifiers it
presses, it releases, and it never presses one that is already down. -/
theorem step_balanced (cfg : Config) (st : State) (ev : InputEvent)
    (hm : st.mode.isInsert = false) (hdir : ev.dir = .down)
    (ht : (ev.key == cfg.toggleKey) = false) : Balanced (step cfg st ev).2 := by
  rw [step, hdir]
  simp only [ht, Bool.false_eq_true, if_false, hm]
  split
  · exact balanced_nil
  · exact emitChords_balanced _

/-- **No stray releases.**  A key-up is forwarded only for a key whose key-down
CapslockMode forwarded; everything else is swallowed.  Applications therefore
never see a release for a key they never saw pressed. -/
theorem up_only_if_pressed (cfg : Config) (st : State) (ev : InputEvent)
    (hdir : ev.dir = .up) (hn : ev.key ∉ st.down) :
    (step cfg st ev).2 = [] := by
  rw [step, hdir]
  simp [hn]

/-- **No stuck keys, the other half.**  A press that is forwarded is recorded,
so its release will be forwarded too — even if Caps Lock is pressed in
between. -/
theorem down_remembered (cfg : Config) (st : State) (ev : InputEvent)
    (hdir : ev.dir = .down) (hm : st.mode.isInsert = true)
    (ht : (ev.key == cfg.toggleKey) = false)
    (he : (cfg.escapeToNormal && ev.key == PhysKey.key .esc) = false) :
    ev.key ∈ (step cfg st ev).1.down := by
  rw [step, hdir]
  simp only [ht, Bool.false_eq_true, if_false, hm, if_true, he, State.press]
  split
  · next h => simpa using h
  · simp

/-- Balance is preserved across a whole session, so a long run of commands
cannot accumulate a stuck modifier either. -/
theorem run_balanced (cfg : Config) (st : State) (evs : List InputEvent)
    (hdir : ∀ ev ∈ evs, ev.dir = .down)
    (ht : ∀ ev ∈ evs, (ev.key == cfg.toggleKey) = false)
    (h : ∀ st' ev, st'.mode.isInsert = false → (step cfg st' ev).1.mode.isInsert = false)
    (h₀ : st.mode.isInsert = false) : Balanced (run cfg st evs).2 := by
  induction evs generalizing st with
  | nil => exact balanced_nil
  | cons ev evs ih =>
    rw [run]
    refine (step_balanced cfg st ev h₀ (hdir ev (by simp)) (ht ev (by simp))).append ?_
    exact ih _ (fun e he => hdir e (by simp [he])) (fun e he => ht e (by simp [he])) (h st ev h₀)

/-! ## Insert mode is transparent

The strongest thing CapslockMode can say about itself is what it does when it
is switched off: nothing whatsoever. -/

/-- In insert mode every key press is passed through unchanged. -/
theorem step_insert (cfg : Config) (st : State) (ev : InputEvent)
    (hdir : ev.dir = .down)
    (hm : st.mode.isInsert = true)
    (htoggle : (ev.key == cfg.toggleKey) = false)
    (hesc : (cfg.escapeToNormal && ev.key == PhysKey.key .esc) = false) :
    step cfg st ev = (st.press ev.key, [ev.passthrough]) := by
  rw [step, hdir]
  simp only [htoggle, Bool.false_eq_true, if_false, hm, if_true, hesc]

/-- ... and therefore a whole stream is passed through unchanged. -/
theorem run_insert_transparent (cfg : Config) (st : State) (evs : List InputEvent)
    (hm : st.mode.isInsert = true)
    (hdir : ∀ ev ∈ evs, ev.dir = .down)
    (htoggle : ∀ ev ∈ evs, (ev.key == cfg.toggleKey) = false)
    (hesc : ∀ ev ∈ evs, (cfg.escapeToNormal && ev.key == PhysKey.key .esc) = false) :
    (run cfg st evs).2 = evs.map InputEvent.passthrough := by
  induction evs generalizing st with
  | nil => rfl
  | cons ev evs ih =>
    have hstep := step_insert cfg st ev (hdir ev (by simp)) hm (htoggle ev (by simp))
      (hesc ev (by simp))
    have hmode : (st.press ev.key).mode.isInsert = true := by
      unfold State.press; split <;> exact hm
    have hrest := ih (st.press ev.key) hmode (fun e he => hdir e (by simp [he]))
      (fun e he => htoggle e (by simp [he])) (fun e he => hesc e (by simp [he]))
    simp [run, hstep, hrest]

/-! ## Caps Lock -/

/-- The modes you are in when nothing is half-done. -/
def SettledMode : Type := {m : Mode // m.isVisual = false}

/-- Caps Lock, as a map on settled modes. -/
def SettledMode.toggle (m : SettledMode) : SettledMode :=
  ⟨m.1.toggle, by cases m.1 <;> rfl⟩

/-- **Caps Lock is an involution**: press it twice and you are exactly where
you started. -/
theorem SettledMode.toggle_involutive : Function.Involutive SettledMode.toggle := by
  rintro ⟨m, hm⟩
  cases m with
  | insert => rfl
  | normal => rfl
  | visual b => simp [Mode.isVisual] at hm

/-- Pressing the toggle key flips the mode, forgets any half-typed command, and
types nothing. -/
theorem step_toggle_down (cfg : Config) (st : State) (mods : Mods) :
    step cfg st { dir := .down, key := cfg.toggleKey, mods := mods } = (st.toggleMode, []) := by
  simp [step]

/-- Releasing it does nothing at all. -/
theorem step_toggle_up (cfg : Config) (st : State) (mods : Mods)
    (hn : cfg.toggleKey ∉ st.down) :
    step cfg st { dir := .up, key := cfg.toggleKey, mods := mods } = (st, []) := by
  simp [step, hn]

/-- Caps Lock never types anything. -/
theorem capsLock_silent (cfg : Config) (st : State) (dir : Dir) (mods : Mods)
    (hn : cfg.toggleKey ∉ st.down) :
    (step cfg st { dir := dir, key := cfg.toggleKey, mods := mods }).2 = [] := by
  cases dir
  · rw [step_toggle_down]
  · rw [step_toggle_up _ _ _ hn]

/-- Two taps of Caps Lock are a reset: they emit nothing, they throw away any
half-typed command, and — unless you were in the middle of a selection — they
put you back in the mode you started in. -/
theorem capsLock_twice (cfg : Config) (st : State) (mods : Mods)
    (hn : cfg.toggleKey ∉ st.down) :
    let ev : InputEvent := { dir := .down, key := cfg.toggleKey, mods := mods }
    let st₁ := (step cfg st ev).1
    let st₂ := (step cfg st₁ ev).1
    (step cfg st ev).2 = [] ∧ (step cfg st₁ ev).2 = [] ∧
      st₂.pending = .idle ∧ st₂.count = 0 ∧
      (st.mode.isVisual = false → st₂.mode = st.mode) := by
  intro ev st₁ st₂
  have h₁ : st₁ = st.toggleMode := by simp [st₁, ev, step_toggle_down]
  have h₂ : st₂ = st.toggleMode.toggleMode := by simp [st₂, ev, h₁, step_toggle_down]
  refine ⟨capsLock_silent cfg st .down mods hn, capsLock_silent cfg st₁ .down mods (by simp [h₁, State.toggleMode, hn]), by simp [h₂, State.toggleMode], by simp [h₂, State.toggleMode], ?_⟩
  intro hv
  rw [h₂]
  cases hm : st.mode with
  | insert => simp [State.toggleMode, Mode.toggle, hm]
  | normal => simp [State.toggleMode, Mode.toggle, hm]
  | visual b => rw [hm] at hv; simp [Mode.isVisual] at hv

/-! ## Escape -/

/-- Escape always lands you in normal mode with a clean slate, from any state,
without typing anything.  This is the "get me out of here" guarantee. -/
theorem esc_resets (cfg : Config) (st : State) (mods : Mods)
    (hm : st.mode.isInsert = false) (htoggle : (PhysKey.key Key.esc == cfg.toggleKey) = false) :
    step cfg st { dir := .down, key := .key .esc, mods := mods } = (st.toNormal, []) := by
  simp [step, htoggle, hm, InputEvent.chord?, command, State.toNormal, Response.commit,
    Response.emit, Response.chords, emitChords, State.toggleMode]

/-! ## Bounded work

`maxCount` is the promise that no key press can turn into an unbounded number
of synthetic events. -/

@[simp] theorem toNormal_count (st : State) : st.toNormal.count = 0 := rfl
@[simp] theorem toInsert_count (st : State) : st.toInsert.count = 0 := rfl
@[simp] theorem toVisual_count (st : State) (b : Bool) : (st.toVisual b).count = 0 := rfl
@[simp] theorem waiting_count (st : State) (p : Pending) : (st.waiting p).count = 0 := rfl
@[simp] theorem toggleMode_count (st : State) : st.toggleMode.count = 0 := rfl
@[simp] theorem press_count (st : State) (k : PhysKey) : (st.press k).count = st.count := by
  unfold State.press; split <;> rfl
@[simp] theorem release_count (st : State) (k : PhysKey) : (st.release k).count = st.count := rfl
@[simp] theorem clamp_le (cfg : Config) (n : Nat) : cfg.clamp n ≤ cfg.maxCount :=
  Nat.min_le_right _ _

@[simp] theorem linewise_count (cfg : Config) (st : State) (op : Operator) (n : Nat) :
    (linewise cfg st op n).state.count = 0 := by
  unfold linewise; split <;> rfl

@[simp] theorem applyOver_count (st : State) (op : Operator) (b bd : List Chord) (r : Nat) :
    (applyOver st op b bd r).state.count = 0 := by
  unfold applyOver; split_ifs <;> rfl

theorem gotoLine_count (e f : Bool) (st : State) (n : Nat) :
    (gotoLine e f st n).state.count ≤ st.count := by
  unfold gotoLine
  split_ifs <;> simp [State.toNormal, State.waiting]

@[simp] theorem commit_count (r : Response) : r.commit.count = r.state.count := by
  unfold Response.commit; split <;> rfl

/-- The count never exceeds `maxCount`, however many digits you type. -/
theorem command_count_le (cfg : Config) (st : State) (c : Chord) (h : st.count ≤ cfg.maxCount) :
    (command cfg st c).state.count ≤ cfg.maxCount := by
  have hgoto : ∀ e f n, (gotoLine e f st n).state.count ≤ cfg.maxCount := fun e f n =>
    le_trans (gotoLine_count e f st n) h
  unfold command replaceCmd gCmd textObjCmd operatorCmd visualCmd normalCmd
  repeat' split
  all_goals try exact hgoto _ _ _
  all_goals try exact h
  all_goals try split_ifs
  all_goals try simp [State.toNormal, State.toInsert, State.toVisual, State.waiting, Config.clamp]
  all_goals try (split <;> simp [State.toNormal, State.toInsert, State.toVisual, State.waiting])
  all_goals try omega

/-- And so it never exceeds `maxCount` while the machine is running. -/
theorem step_count_le (cfg : Config) (st : State) (ev : InputEvent) (h : st.count ≤ cfg.maxCount) :
    (step cfg st ev).1.count ≤ cfg.maxCount := by
  unfold step
  repeat' split
  all_goals try simp only [commit_count]
  all_goals try exact command_count_le cfg st _ h
  all_goals try exact h
  all_goals try simp [State.release, State.toggleMode]
  all_goals try (split_ifs <;> simp)
  all_goals try omega
  all_goals try exact h

/-- A response plays `before`, then `body` `repeats` times, then `after`. -/
theorem Response.chords_length (r : Response) :
    r.chords.length = r.before.length + r.repeats * r.body.length + r.after.length := by
  simp [Response.chords, List.length_flatten, List.map_replicate, List.sum_replicate]
  omega

/-- No key press ever repeats its keystrokes more than `maxCount` times: this is
what stops a slipped `99999dd` from becoming a storm of synthetic events. -/
theorem command_repeats_le (cfg : Config) (st : State) (c : Chord) (h : st.count ≤ cfg.maxCount) :
    (command cfg st c).repeats ≤ max cfg.maxCount 1 := by
  have hgoto : ∀ e f, (gotoLine e f st st.count).repeats ≤ max cfg.maxCount 1 := by
    intro e f
    unfold gotoLine
    split_ifs <;> simp <;> omega
  unfold command replaceCmd gCmd textObjCmd operatorCmd visualCmd normalCmd linewise applyOver
    Config.clamp
  repeat' split
  all_goals try exact hgoto _ _
  all_goals try split_ifs
  all_goals try simp [Config.clamp]
  all_goals try (split <;> simp [Config.clamp])
  all_goals try omega

/-- Together with `Chord.emit_length_le`, that bounds the work one key press can
cause: at most `10 * (before + maxCount * body + after)` events. -/
theorem step_emit_length_le (cfg : Config) (st : State) (ev : InputEvent) (c : Chord)
    (hd : ev.dir = .down) (hc : ev.chord? = some c) (hi : st.mode.isInsert = false)
    (ht : (ev.key == cfg.toggleKey) = false) :
    (step cfg st ev).2.length ≤ 10 * (command cfg st c).chords.length := by
  have : (step cfg st ev).2 = emitChords (command cfg st c).chords := by
    simp [step, ht, hi, hd, hc, Response.emit]
  rw [this]
  induction (command cfg st c).chords with
  | nil => simp [emitChords]
  | cons x xs ih =>
    rw [emitChords, List.flatMap_cons, List.length_append]
    have := Chord.emit_length_le x
    simp only [emitChords] at ih
    simp only [List.length_cons]
    omega

/-! ## Half-typed commands always resolve -/

/-- The digits, as the count parser sees them. -/
def Chord.isDigit (c : Chord) : Bool :=
  match c.key with
  | .char ch => ('1' ≤ ch && ch ≤ '9') || ch == '0'
  | _ => false

theorem countDigit?_eq_none {st : State} {c : Chord} (h : c.isDigit = false) :
    countDigit? st c = none := by
  unfold countDigit?
  split
  · rfl
  · unfold Chord.isDigit at h
    split
    · next ch heq =>
      rw [heq, Bool.or_eq_false_iff] at h
      simp [h.1, h.2]
    · rfl

/-- A waiting operator always moves on: it either fires, or upgrades to a text
object (which resolves next key).  It can never stay an operator, so `d` cannot
swallow your keyboard. -/
theorem operator_progress (cfg : Config) (st : State) (op : Operator) (n : Nat) (c : Chord)
    (hd : c.isDigit = false) (hp : st.pending = .operator op n) :
    (command cfg st c).state.pending = .idle ∨
      ∃ op' n' b, (command cfg st c).state.pending = .textObj op' n' b := by
  unfold command
  rw [hp]
  split
  · exact Or.inl rfl
  · rw [countDigit?_eq_none hd]
    unfold operatorCmd linewise applyOver
    repeat' split
    all_goals try contradiction
    all_goals try exact Or.inl rfl
    all_goals try exact Or.inr ⟨_, _, _, rfl⟩
    all_goals try simp [State.toNormal, State.toInsert, State.waiting]

/-- A text object resolves immediately. -/
theorem textObj_progress (cfg : Config) (st : State) (op : Operator) (n : Nat) (b : Bool)
    (c : Chord) (hd : c.isDigit = false) (hp : st.pending = .textObj op n b) :
    (command cfg st c).state.pending = .idle := by
  unfold command
  rw [hp]
  split
  · rfl
  · rw [countDigit?_eq_none hd]
    unfold textObjCmd applyOver
    repeat' split
    all_goals try contradiction
    all_goals try rfl
    all_goals try simp [State.toNormal, State.toInsert]

/-- `r` resolves immediately too. -/
theorem replace_progress (cfg : Config) (st : State) (c : Chord) (hp : st.pending = .replace) :
    (command cfg st c).state.pending = .idle := by
  unfold command replaceCmd
  rw [hp]
  repeat' split
  all_goals try contradiction
  all_goals try rfl
  all_goals try simp [State.toNormal]

end CapslockMode
