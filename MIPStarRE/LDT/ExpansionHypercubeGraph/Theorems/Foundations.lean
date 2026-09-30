import MIPStarRE.LDT.ExpansionHypercubeGraph.MatrixRealization.TraceForms

/-!
# Section 7 hypercube graph: trace-form foundations

This file provides the abstract theorem statements and trace-form identities
used to formalize the local and global variance rewrites in Section 7 of the LDT
paper.  The concrete matrix-realization statements are proved first; the
public-facing statements in `MIPStarRE.LDT.ExpansionHypercubeGraph.Theorems.Results`
then specialize these identities to arbitrary finite-dimensional operator
families.

## References

- `references/ldt-paper/expansion.tex`, especially `lem:local-rewrite` and
  `lem:global-rewrite`
- `blueprint/src/chapter/ch05_expansion.tex`
-/

namespace MIPStarRE.LDT.ExpansionHypercubeGraph

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-! ## Statement structures and matrix realization -/

/-- Reinterpret an abstract operator family and quantum state as the concrete
matrix realization used by the trace-form proof of Section 7. -/
def abstractMatrixModel (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) [Nonempty ι] :
    MatrixOperatorFamilyRealization params where
  space :=
    { carrier := ι
      instFintype := inferInstance
      instDecidableEq := inferInstance
      instNonempty := inferInstance }
  state :=
    { matrix := ψ.density
      positive := ψ.density_psd }
  family := A

/-- If the ambient outcome type is empty, the abstract local variance is zero. -/
lemma localVariance_eq_zero_of_isEmpty (hι : ¬ Nonempty ι) (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) :
    localVariance params A ψ = 0 := by
  haveI : IsEmpty ι := not_nonempty_iff.mp hι
  have hzero : ∀ uv : Point params × Point params,
      ev ψ (pointDifferenceSquaredOperator A uv.1 uv.2) = 0 := by
    intro uv
    simp [pointDifferenceSquaredOperator, ev, MIPStarRE.Quantum.normalizedTrace]
  unfold localVariance
  rw [avgOver_congr _ _ (fun _ => 0) hzero, avgOver_zero]
  ring

/-- If the ambient outcome type is empty, the abstract global variance is zero. -/
lemma globalVariance_eq_zero_of_isEmpty (hι : ¬ Nonempty ι) (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) :
    globalVariance params A ψ = 0 := by
  haveI : IsEmpty ι := not_nonempty_iff.mp hι
  have hzero : ∀ uv : Point params × Point params,
      ev ψ (pointDifferenceSquaredOperator A uv.1 uv.2) = 0 := by
    intro uv
    simp [pointDifferenceSquaredOperator, ev, MIPStarRE.Quantum.normalizedTrace]
  unfold globalVariance
  rw [avgOver_congr _ _ (fun _ => 0) hzero, avgOver_zero]
  ring

/-! ## Finite-sum helper lemmas -/

/-- Factor a common scalar out of a doubly indexed finite sum. -/
lemma sum_sum_mul_left {α β γ : Type*}
    [Fintype α] [Fintype β] [CommSemiring γ] (c : γ) (f : α → β → γ) :
    ∑ a, ∑ b, c * f a b = c * ∑ a, ∑ b, f a b := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro a ha
  rw [Finset.mul_sum]

/-- Distribute a doubly indexed sum across pointwise addition. -/
lemma sum_sum_add {α β γ : Type*}
    [Fintype α] [Fintype β] [AddCommMonoid γ] (f g : α → β → γ) :
    ∑ a, ∑ b, (f a b + g a b) = (∑ a, ∑ b, f a b) + ∑ a, ∑ b, g a b := by
  calc
    ∑ a, ∑ b, (f a b + g a b) = ∑ a, ((∑ b, f a b) + ∑ b, g a b) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      rw [Finset.sum_add_distrib]
    _ = (∑ a, ∑ b, f a b) + ∑ a, ∑ b, g a b := by
      rw [Finset.sum_add_distrib]

/-- Distribute a doubly indexed sum across pointwise subtraction. -/
lemma sum_sum_sub {α β γ : Type*}
    [Fintype α] [Fintype β] [AddCommGroup γ] (f g : α → β → γ) :
    ∑ a, ∑ b, (f a b - g a b) = (∑ a, ∑ b, f a b) - ∑ a, ∑ b, g a b := by
  calc
    ∑ a, ∑ b, (f a b - g a b) = ∑ a, ∑ b, (f a b + (-g a b)) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      refine Finset.sum_congr rfl ?_
      intro b hb
      rw [sub_eq_add_neg]
    _ = (∑ a, ∑ b, f a b) + ∑ a, ∑ b, (-g a b) := by
      exact sum_sum_add (f := f) (g := fun a b => -g a b)
    _ = (∑ a, ∑ b, f a b) - ∑ a, ∑ b, g a b := by
      simp [sub_eq_add_neg]

/-! ## Trace witness closed forms -/

/-- Turn a matrix realization state into the corresponding abstract quantum state. -/
def matrixModelState {params : Parameters}
    (model : MatrixOperatorFamilyRealization params) : QuantumState model.space.carrier where
  density := model.state.matrix
  density_psd := model.state.positive

private lemma trace_combined_tensor_eq (params : Parameters)
    (model : MatrixOperatorFamilyRealization params)
    (P : MatrixOperator (pointHilbertSpace params)) :
    (((matrixCombinedOperator params model)ᴴ *
        (matrixTensorOperator P model.state.matrix * matrixCombinedOperator params model)).trace) =
      ∑ u, ∑ v,
        P u v * (model.state.matrix * ((model.family v)ᴴ * model.family u)).trace := by
  rw [Matrix.trace_mul_comm]
  suffices
      ∑ a : (tensorHilbertSpace (pointHilbertSpace params) model.space).carrier,
        ∑ b : model.space.carrier,
        ((matrixTensorOperator P model.state.matrix *
          matrixCombinedOperator params model) a b) *
          model.family a.1 b a.2 =
        ∑ u, ∑ v, P u v *
          ∑ i, (model.state.matrix * ((model.family v)ᴴ * model.family u)).diag i by
    simpa [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
      matrixCombinedOperator, mul_assoc] using this
  let f : (Point params × model.space.carrier) → model.space.carrier →
      (Point params × model.space.carrier) → ℂ :=
    fun x i z => P x.1 z.1 * model.state.matrix x.2 z.2 *
      (starRingEnd ℂ) (model.family z.1 i z.2)
  let g : (Point params × model.space.carrier) → model.space.carrier → ℂ :=
    fun x i => model.family x.1 i x.2
  change ∑ a, ∑ b, (∑ c, f a b c) * g a b = _
  simp_rw [Finset.sum_mul]
  simp_rw [f, g, Fintype.sum_prod_type, Finset.mul_sum]
  conv =>
    rhs
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum, mul_assoc]
  refine Finset.sum_congr rfl ?_
  intro x hx
  calc
    ∑ x₁, ∑ x₂, ∑ x₃, ∑ x₄,
        P x x₃ * model.state.matrix x₁ x₄ *
          (starRingEnd ℂ) (model.family x₃ x₂ x₄) * model.family x x₂ x₁
      = ∑ x₁, ∑ x₃, ∑ x₂, ∑ x₄,
          P x x₃ * model.state.matrix x₁ x₄ *
            (starRingEnd ℂ) (model.family x₃ x₂ x₄) * model.family x x₂ x₁ := by
          refine Finset.sum_congr rfl ?_
          intro x₁ _
          rw [Finset.sum_comm]
    _ = ∑ x₃, ∑ x₁, ∑ x₂, ∑ x₄,
          P x x₃ * model.state.matrix x₁ x₄ *
            (starRingEnd ℂ) (model.family x₃ x₂ x₄) * model.family x x₂ x₁ := by
          rw [Finset.sum_comm]
    _ = ∑ x₃, ∑ x₁, ∑ x₄, ∑ x₂,
          P x x₃ * model.state.matrix x₁ x₄ *
            (starRingEnd ℂ) (model.family x₃ x₂ x₄) * model.family x x₂ x₁ := by
          refine Finset.sum_congr rfl ?_
          intro x₃ _
          refine Finset.sum_congr rfl ?_
          intro x₁ _
          rw [Finset.sum_comm]
    _ = ∑ x₁, ∑ x₂, ∑ x₃, ∑ i,
          P x x₁ *
            (model.state.matrix x₂ x₃ *
              ((starRingEnd ℂ) (model.family x₁ i x₃) * model.family x i x₂)) := by
          simp [mul_assoc, mul_left_comm, mul_comm]

/-- Expand the normalized trace of the combined tensor witness into its explicit
double-sum form. -/
lemma normalizedTrace_combined_tensor_eq (params : Parameters)
    (model : MatrixOperatorFamilyRealization params)
    (P : MatrixOperator (pointHilbertSpace params)) :
    MIPStarRE.Quantum.normalizedTrace
      ((matrixCombinedOperator params model)ᴴ *
        (matrixTensorOperator P model.state.matrix * matrixCombinedOperator params model)) =
      ∑ u, ∑ v,
        P u v * matrixExpectation model.state ((model.family v)ᴴ * model.family u) := by
  unfold MIPStarRE.Quantum.normalizedTrace matrixExpectation
  rw [trace_combined_tensor_eq]
  simp_rw [div_eq_mul_inv]
  simp [MIPStarRE.Quantum.normalizedTrace, Finset.sum_mul, div_eq_mul_inv, mul_assoc]

end MIPStarRE.LDT.ExpansionHypercubeGraph
