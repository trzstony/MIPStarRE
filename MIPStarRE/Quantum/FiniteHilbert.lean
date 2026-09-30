import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite-dimensional Hilbert spaces

Small reusable facts about matrices acting on finite-dimensional Hilbert
spaces, independent of the low individual degree test.

## Main results

* `Matrix.toEuclideanLin_conjTranspose_mul_self`: the Euclidean linear map of
  `Aᴴ * A` is the adjoint composition of the linear map of `A` with itself.
-/

open Module

namespace Matrix

/-- The matrix of an adjoint product is the adjoint-composition of the
corresponding Euclidean linear map. -/
theorem toEuclideanLin_conjTranspose_mul_self
    {𝕜 : Type*} [RCLike 𝕜]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜) :
    Matrix.toEuclideanLin (Aᴴ * A) =
      (Matrix.toEuclideanLin A).adjoint.comp (Matrix.toEuclideanLin A) := by
  classical
  rw [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same (p := (2 : ENNReal)),
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint]

end Matrix
