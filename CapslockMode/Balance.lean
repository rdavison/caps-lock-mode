/-
# No stuck keys

The classic way a keyboard remapper ruins somebody's afternoon is by leaving a
modifier down: it synthesises `Ctrl` press, something goes sideways, the
matching release never happens, and from then on every keystroke is a shortcut.
Testing does not really help here, because the bad paths are exactly the ones
nobody thought to test.

So instead we prove it.  For a stream of events and a physical key `k`, `net k`
counts presses minus releases.  A stream is `Balanced` when

* every prefix has `net k ∈ {0, 1}` — the key is never released while up, and
  never pressed twice without a release in between; and
* the whole stream has `net k = 0` — nothing is left held.

The main theorem, `step_balanced`, says that every event stream CapslockMode
synthesises is balanced, for every key, from every state, for every input.
-/
import CapslockMode.Prelude
import CapslockMode.Key

namespace CapslockMode

/-- `+1` for a press of `k`, `-1` for a release of `k`, `0` for other keys. -/
def OutputEvent.delta (k : PhysKey) (e : OutputEvent) : ℤ :=
  if e.key = k then (match e.dir with | .down => 1 | .up => -1) else 0

/-- Presses minus releases of `k` in a stream. -/
def net (k : PhysKey) (l : List OutputEvent) : ℤ := (l.map (OutputEvent.delta k)).sum

/-- A stream that holds no key down at the end and never gets confused about
whether a key is currently down. -/
structure Balanced (l : List OutputEvent) : Prop where
  /-- Along the way, every key is either up or held exactly once. -/
  sane : ∀ (k : PhysKey) (p : List OutputEvent), p <+: l → 0 ≤ net k p ∧ net k p ≤ 1
  /-- At the end, nothing is held. -/
  settled : ∀ k : PhysKey, net k l = 0

/-! ## Arithmetic of `net` -/

@[simp] theorem net_nil (k : PhysKey) : net k [] = 0 := rfl

@[simp] theorem net_cons (k : PhysKey) (e : OutputEvent) (l : List OutputEvent) :
    net k (e :: l) = e.delta k + net k l := by
  simp [net]

@[simp] theorem net_append (k : PhysKey) (l₁ l₂ : List OutputEvent) :
    net k (l₁ ++ l₂) = net k l₁ + net k l₂ := by
  simp [net]

@[simp] theorem net_singleton (k : PhysKey) (e : OutputEvent) :
    net k [e] = e.delta k := by
  simp [net]

theorem delta_eq_zero_of_ne {k : PhysKey} {e : OutputEvent} (h : e.key ≠ k) :
    e.delta k = 0 := by
  simp [OutputEvent.delta, h]

@[simp] theorem delta_down_self (k : PhysKey) : (OutputEvent.down k).delta k = 1 := by
  simp [OutputEvent.delta, OutputEvent.down]

@[simp] theorem delta_up_self (k : PhysKey) : (OutputEvent.up k).delta k = -1 := by
  simp [OutputEvent.delta, OutputEvent.up]

theorem delta_down_of_ne {k k' : PhysKey} (h : k' ≠ k) : (OutputEvent.down k).delta k' = 0 :=
  delta_eq_zero_of_ne (k := k') (e := OutputEvent.down k) (Ne.symm h)

theorem delta_up_of_ne {k k' : PhysKey} (h : k' ≠ k) : (OutputEvent.up k).delta k' = 0 :=
  delta_eq_zero_of_ne (k := k') (e := OutputEvent.up k) (Ne.symm h)

/-- If `k` never occurs in `l`, the stream says nothing about `k`. -/
theorem net_eq_zero_of_not_mem {k : PhysKey} {l : List OutputEvent}
    (h : ∀ e ∈ l, e.key ≠ k) : net k l = 0 := by
  induction l with
  | nil => simp
  | cons e l ih =>
    rw [net_cons, delta_eq_zero_of_ne (h e (by simp)), ih (fun e he => h e (by simp [he])), add_zero]

/-! ## Prefixes -/

theorem prefix_singleton {α : Type _} {p : List α} {a : α} (h : p <+: [a]) :
    p = [] ∨ p = [a] := by
  rcases List.prefix_cons_iff.mp h with rfl | ⟨t, rfl, ht⟩
  · exact Or.inl rfl
  · rw [List.prefix_nil.mp ht]; exact Or.inr rfl

theorem prefix_pair {α : Type _} {p : List α} {a b : α} (h : p <+: [a, b]) :
    p = [] ∨ p = [a] ∨ p = [a, b] := by
  rcases List.prefix_cons_iff.mp h with rfl | ⟨t, rfl, ht⟩
  · exact Or.inl rfl
  · rcases prefix_singleton ht with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

/-- Splitting a prefix of a concatenation. -/
theorem prefix_append_cases {l₁ l₂ p : List OutputEvent} (h : p <+: l₁ ++ l₂) :
    p <+: l₁ ∨ ∃ q, q <+: l₂ ∧ p = l₁ ++ q := by
  rcases (List.prefix_or_prefix_of_prefix h (List.prefix_append l₁ l₂)) with h' | h'
  · exact Or.inl h'
  · obtain ⟨q, rfl⟩ := h'
    exact Or.inr ⟨q, (List.prefix_append_right_inj l₁).mp h, rfl⟩

/-! ## Balanced streams -/

theorem balanced_nil : Balanced [] where
  sane := by
    intro k p hp
    rw [List.prefix_nil.mp hp]
    simp
  settled := by simp

/-- Playing one balanced stream after another is balanced: each one starts and
ends with nothing held, so they cannot interfere. -/
theorem Balanced.append {l₁ l₂ : List OutputEvent} (h₁ : Balanced l₁) (h₂ : Balanced l₂) :
    Balanced (l₁ ++ l₂) where
  sane := by
    intro k p hp
    rcases prefix_append_cases hp with hp' | ⟨q, hq, rfl⟩
    · exact h₁.sane k p hp'
    · rw [net_append, h₁.settled k, zero_add]
      exact h₂.sane k q hq
  settled := by
    intro k
    rw [net_append, h₁.settled k, h₂.settled k, add_zero]

/-- Tapping a key is balanced: press, release, nothing held. -/
theorem balanced_tap (k : PhysKey) : Balanced (tap k) where
  sane := by
    intro k' p hp
    rcases prefix_pair hp with rfl | rfl | rfl
    · simp
    · by_cases hk : k' = k
      · subst hk; simp
      · simp [delta_down_of_ne hk]
    · by_cases hk : k' = k
      · subst hk; simp [tap]
      · simp [tap, delta_down_of_ne hk, delta_up_of_ne hk]
  settled := by
    intro k'
    by_cases hk : k' = k
    · subst hk; simp [tap]
    · simp [tap, delta_down_of_ne hk, delta_up_of_ne hk]

/-- Press, do something, release.  The `hfresh` hypothesis — that the wrapped
stream never mentions `k` itself — is exactly what rules out pressing a
modifier that is already down. -/
theorem balanced_wrap {k : PhysKey} {l : List OutputEvent} (h : Balanced l)
    (hfresh : ∀ e ∈ l, e.key ≠ k) : Balanced (wrap k l) where
  sane := by
    have hzero : net k l = 0 := net_eq_zero_of_not_mem hfresh
    intro k' p hp
    rw [wrap] at hp
    rcases List.prefix_cons_iff.mp hp with rfl | ⟨t, rfl, ht⟩
    · simp
    · rcases prefix_append_cases ht with ht' | ⟨r, hr, rfl⟩
      · by_cases hk : k' = k
        · subst hk
          rw [net_cons, delta_down_self,
            net_eq_zero_of_not_mem (fun e he => hfresh e (ht'.subset he))]
          norm_num
        · rw [net_cons, delta_down_of_ne hk, zero_add]
          exact h.sane k' t ht'
      · rcases prefix_singleton hr with rfl | rfl
        · by_cases hk : k' = k
          · subst hk; rw [net_cons, delta_down_self, net_append, hzero]; norm_num
          · rw [net_cons, delta_down_of_ne hk, net_append, h.settled k']; norm_num
        · by_cases hk : k' = k
          · subst hk
            rw [net_cons, delta_down_self, net_append, hzero, net_singleton, delta_up_self]
            norm_num
          · rw [net_cons, delta_down_of_ne hk, net_append, h.settled k', net_singleton,
              delta_up_of_ne hk]
            norm_num
  settled := by
    have hzero : net k l = 0 := net_eq_zero_of_not_mem hfresh
    intro k'
    by_cases hk : k' = k
    · subst hk
      rw [wrap, net_cons, delta_down_self, net_append, hzero, net_singleton, delta_up_self]
      norm_num
    · rw [wrap, net_cons, delta_down_of_ne hk, net_append, h.settled k', net_singleton,
        delta_up_of_ne hk]
      norm_num

/-! ## Chords -/

/-- Which keys a `foldr wrap` stream can possibly mention. -/
theorem mem_foldr_wrap {ms : List Modifier} {k : Key} {e : OutputEvent}
    (h : e ∈ ms.foldr (fun m l => wrap (.mod m) l) (tap (.key k))) :
    e.key = PhysKey.key k ∨ ∃ m ∈ ms, e.key = PhysKey.mod m := by
  induction ms with
  | nil =>
    rcases List.mem_cons.mp h with rfl | h'
    · exact Or.inl rfl
    · rcases List.mem_singleton.mp h' with rfl
      exact Or.inl rfl
  | cons m ms ih =>
    rw [List.foldr_cons, wrap] at h
    rcases List.mem_cons.mp h with rfl | h'
    · exact Or.inr ⟨m, by simp, rfl⟩
    · rcases List.mem_append.mp h' with h'' | h''
      · rcases ih h'' with hk | ⟨m', hm', hkey⟩
        · exact Or.inl hk
        · exact Or.inr ⟨m', by simp [hm'], hkey⟩
      · rcases List.mem_singleton.mp h'' with rfl
        exact Or.inr ⟨m, by simp, rfl⟩

/-- Holding a duplicate-free list of modifiers around a key tap is balanced.
Duplicate freedom is what rules out pressing `Ctrl` twice; the fact that `Key`
and `Modifier` are different types is what rules out the inner key colliding
with one of the modifiers. -/
theorem balanced_foldr_wrap {ms : List Modifier} (hnd : ms.Nodup) (k : Key) :
    Balanced (ms.foldr (fun m l => wrap (.mod m) l) (tap (.key k))) := by
  induction ms with
  | nil => exact balanced_tap _
  | cons m ms ih =>
    rw [List.foldr_cons]
    refine balanced_wrap (ih hnd.of_cons) ?_
    intro e he hcontra
    rcases mem_foldr_wrap he with hk | ⟨m', hm', hkey⟩
    · rw [hk] at hcontra; exact PhysKey.noConfusion hcontra
    · rw [hkey] at hcontra
      exact (List.nodup_cons.mp hnd).1 (by cases PhysKey.mod.inj hcontra; exact hm')

/-- The modifiers of a `Mods` are duplicate free — there is only one `Ctrl`. -/
theorem Mods.held_nodup (m : Mods) : m.held.Nodup := by
  obtain ⟨c, a, s, p⟩ := m
  cases c <;> cases a <;> cases s <;> cases p <;> simp [Mods.held]

/-- **Every chord CapslockMode can play is balanced.** -/
theorem Chord.emit_balanced (c : Chord) : Balanced c.emit :=
  balanced_foldr_wrap c.mods.held_nodup c.key

/-! ## How much a chord costs -/

theorem foldr_wrap_length (ms : List Modifier) (k : Key) :
    (ms.foldr (fun m l => wrap (.mod m) l) (tap (.key k))).length = 2 * ms.length + 2 := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    rw [List.foldr_cons, wrap]
    simp only [List.length_cons, List.length_append, List.length_nil, ih]
    omega

/-- A chord is at most ten events: four modifiers down, a key down and up, four
modifiers up. -/
theorem Chord.emit_length (c : Chord) : c.emit.length = 2 * c.mods.count + 2 :=
  foldr_wrap_length _ _

theorem Chord.emit_length_le (c : Chord) : c.emit.length ≤ 10 := by
  rw [Chord.emit_length]
  have : c.mods.count ≤ 4 := by
    obtain ⟨a, b, d, e⟩ := c.mods
    cases a <;> cases b <;> cases d <;> cases e <;> simp [Mods.count, Mods.held]
  omega

/-- Sequences of chords are balanced. -/
theorem emitChords_balanced (cs : List Chord) : Balanced (emitChords cs) := by
  induction cs with
  | nil => exact balanced_nil
  | cons c cs ih =>
    rw [emitChords, List.flatMap_cons]
    exact (Chord.emit_balanced c).append ih

end CapslockMode
