import MIPStarRE.Quantum.FiniteMatrix.Basic

/-!
# Normalized trace, projectors, and spectral truncation

This module contains the normalized trace `τ`, the squared `τ`-norm, the
paper-facing orthogonal-projection name, and the spectral-truncation witness used
in the low individual degree test formalization.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise
open WithLp

namespace MIPStarRE.Quantum

variable {d : Type*} [Fintype d]

/-! ### Normalized trace -/

/-- The normalized trace `τ(A) = tr(A) / |d|`. -/
noncomputable def normalizedTrace (A : Op d) : ℂ :=
  A.trace / (Fintype.card d : ℂ)

/-- The normalized trace of the zero operator is zero. -/
@[simp] theorem normalizedTrace_zero : normalizedTrace (0 : Op d) = 0 := by
  simp [normalizedTrace]

/-- The normalized trace is additive. -/
theorem normalizedTrace_add (A B : Op d) :
    normalizedTrace (A + B) = normalizedTrace A + normalizedTrace B := by
  simp [normalizedTrace, Matrix.trace_add, add_div]

/-- The normalized trace sends subtraction to subtraction. -/
theorem normalizedTrace_sub (A B : Op d) :
    normalizedTrace (A - B) = normalizedTrace A - normalizedTrace B := by
  simp [normalizedTrace, Matrix.trace_sub, sub_div]

/-- Scalar multiplication pulls out of the normalized trace. -/
theorem normalizedTrace_smul (c : ℂ) (A : Op d) :
    normalizedTrace (c • A) = c * normalizedTrace A := by
  simp [normalizedTrace, Matrix.trace_smul]
  ring

/-- The normalized trace is invariant under swapping two multiplicative factors. -/
theorem normalizedTrace_mul_comm (A B : Op d) :
    normalizedTrace (A * B) = normalizedTrace (B * A) := by
  simp only [normalizedTrace]
  rw [Matrix.trace_mul_comm]

/-- Simultaneous reindexing of rows and columns preserves the normalized trace. -/
theorem normalizedTrace_reindex {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂]
    (e : d₁ ≃ d₂) (A : Op d₁) :
    normalizedTrace (Matrix.reindex e e A) = normalizedTrace A := by
  have hcard : Fintype.card d₂ = Fintype.card d₁ := Fintype.card_congr e.symm
  unfold normalizedTrace
  rw [Matrix.trace_reindex]
  simp [hcard]

/-! ### Projector predicate -/

/-- Paper-facing name for Mathlib's predicate that a matrix is a self-adjoint idempotent. -/
abbrev IsProj (P : Op d) : Prop := IsStarProjection P

end MIPStarRE.Quantum
