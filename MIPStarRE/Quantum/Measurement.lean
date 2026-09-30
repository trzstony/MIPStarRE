import MIPStarRE.Quantum.FiniteMatrix.NormalizedTrace

/-!
# Matrix-valued measurements for the MIP*=RE project

This file provides the matrix-valued measurement layer used by the LDT formalization.

## Main definitions

* `Submeasurement` — a family of PSD matrices summing to at most the identity.
* `Measurement` — a family of PSD matrices summing to exactly the identity.

## References

This file builds the project's finite-dimensional measurement layer on top of
the normalized-trace and positive-operator facts in `MIPStarRE.Quantum.FiniteMatrix`
for the quantum formalization in `references/ldt-paper/`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.Quantum

/-! ## Submeasurements and measurements -/

/--
A submeasurement on a finite answer type `α` is a family of PSD matrices
`M : α → Op d` with `∑ a, M a ≤ 1`.
-/
structure Submeasurement (α : Type*) [Fintype α] (d : Type*) [Fintype d] [DecidableEq d] where
  /-- The effect operators. -/
  effect : α → Op d
  /-- Each effect is positive semidefinite. -/
  pos : ∀ a, 0 ≤ effect a
  /-- The effects sum to at most the identity. -/
  sum_le_one : ∑ a, effect a ≤ 1

/--
A measurement is a submeasurement whose effects sum exactly to the identity.
-/
structure Measurement (α : Type*) [Fintype α] (d : Type*) [Fintype d] [DecidableEq d]
    extends Submeasurement α d where
  /-- The effects sum to the identity. -/
  sum_eq_one : ∑ a, effect a = 1

/-! ## Totals and postprocessing -/

namespace Submeasurement

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {α β : Type*} [Fintype α] [Fintype β]

/-! ### Totals and postprocessing -/

/-- The total operator `∑ a, M_a`. -/
noncomputable def total (M : Submeasurement α d) : Op d :=
  ∑ a, M.effect a

end Submeasurement

namespace Measurement

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {α β : Type*} [Fintype α] [Fintype β]

/--
Build a complete measurement from effects whose sum is exactly the identity.

This constructor keeps the equality proof as the primary hypothesis and derives
the inherited submeasurement inequality automatically.  It is useful at paper
sites that are explicitly POVMs rather than relaxed sub-POVMs.
-/
def ofSumEqOne (effect : α → Op d) (pos : ∀ a, 0 ≤ effect a)
    (sum_eq_one : ∑ a, effect a = 1) : Measurement α d where
  effect := effect
  pos := pos
  sum_le_one := le_of_eq sum_eq_one
  sum_eq_one := sum_eq_one

end Measurement

end MIPStarRE.Quantum
