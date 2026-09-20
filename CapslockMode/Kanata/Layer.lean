/-
# The layer stack, and what `_` actually means

The single most misunderstood corner of kanata: **a transparent key does not
fall through to the first layer.  It falls through to `defsrc`.**

The walk is the held layers (newest first), then the base layer, then nothing.
`defsrc` is not a layer in the list -- it is where the walk stops, and it is
never itself transparent, which is why `resolve` is total and has no default
case to argue about.

`delegate-to-first-layer` is the only thing that puts layer 0 into the walk, and
even then only at the bottom, just above `defsrc`.  kanata implements it by
merging layer 0's non-transparent entries into the defsrc layer
(`parser/src/cfg/deflayer.rs`); appending layer 0 to the walk is observationally
the same thing, and much easier to read.

`St` carries the temporary-layer stack and the release obligation in one field,
because they are the same fact.  The stack is `holds.flatMap (·.2.hold)`, and a
release re-uses the action recorded *at press time* rather than re-resolving
against a stack that has since moved.  Re-resolving is the classic stuck-key
bug: you hold a layer key, the layer changes underneath you, and the release
consults the wrong table and emits nothing.  kanata keeps the action per key for
the same reason.
-/
import CapslockMode.Kanata.Config

namespace CapslockMode.Kanata

/-- What the evaluator remembers between events. -/
structure St where
  /-- The layer a press consults when nothing is held. -/
  base : Nat := 0
  /-- Positions currently held, newest first, each with what its press
  resolved to. -/
  holds : List (Nat × Action) := []
  deriving DecidableEq, Repr, Inhabited

/-- The layers a press consults, top first.

`defsrc` is deliberately absent: it is the end of the walk, not a member of
it. -/
def stack (cfg : Cfg n) (st : St) : List Nat :=
  st.holds.flatMap (fun h => h.2.hold) ++
    st.base :: (if cfg.delegateToFirstLayer then [0] else [])

/-- What pressing position `p` means right now.

An out-of-range layer index behaves as transparent, which is what keeps this
total without a `Fin cfg.layers.length` that `Cfg` cannot carry.  The parser is
what actually rules the case out. -/
def resolve (cfg : Cfg n) (st : St) (p : Fin n) : Action :=
  match (stack cfg st).findSome? (fun i => (cfg.layers[i]?).bind (fun L => L.acts[p.val]'p.isLt)) with
  | some a => a
  | none => { keys := [cfg.src[p.val]'p.isLt] }

/-- `resolve` at a position given as a plain number, for callers that have not
already discharged the bound.  `none` is "no such position", never "nothing
happens" -- that is `some {}`. -/
def resolveAt? (cfg : Cfg n) (st : St) (i : Nat) : Option Action :=
  (pos? n i).map (resolve cfg st)

/-! ## What transparency guarantees -/

/-- If every layer the walk consults is transparent at `p`, the answer is the
`defsrc` key.  Stated for an arbitrary stack so that the identity config is a
corollary rather than a separate argument. -/
theorem resolve_transparent (cfg : Cfg n) (st : St) (p : Fin n)
    (h : ∀ i ∈ stack cfg st,
      (cfg.layers[i]?).bind (fun L => L.acts[p.val]'p.isLt) = none) :
    resolve cfg st p = { keys := [cfg.src[p.val]'p.isLt] } := by
  unfold resolve
  rw [List.findSome?_eq_none_iff.mpr h]

/-- The identity config resolves to `defsrc` whatever state it is in: there is
nothing but transparent entries to find, so the stack cannot matter.  Held
layers and a moved base are ruled out here rather than left as an assumption of
the headline result below. -/
theorem resolve_identity_any (src : Vector Code n) (st : St) (p : Fin n) :
    resolve (Cfg.identity src) st p = { keys := [src[p.val]'p.isLt] } := by
  apply resolve_transparent
  intro i _
  match i with
  | 0 => simp [Cfg.identity]
  | _ + 1 => simp [Cfg.identity]

/-- **The headline result.**  A config of one layer of all `_` resolves every
position to its `defsrc` key: it *is* the identity function, with no special
case anywhere.

This is what lets "switched off" stop being a branch in the machine and become
a binding to this evaluator running the identity config. -/
theorem resolve_identity (src : Vector Code n) (p : Fin n) :
    resolve (Cfg.identity src) {} p = { keys := [src[p.val]'p.isLt] } :=
  resolve_identity_any src {} p

end CapslockMode.Kanata
