/-
`CapslockMode.Prelude` fixes the (small) slice of Mathlib that the rest of the
project builds on.  Every other module imports this one, so the Mathlib
dependency surface of CapslockMode is visible in a single file.
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Count
import Mathlib.Data.List.Infix
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Basic
import Mathlib.Order.MinMax
import Mathlib.Tactic.Linarith
