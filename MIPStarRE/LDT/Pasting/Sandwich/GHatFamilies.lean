import MIPStarRE.LDT.Pasting.Defs.Families
import MIPStarRE.LDT.CommutativityPoints.Defs

/-!
# Pasting: completed slice families

Tensor placements of the completed slice measurements `\widehat G^x` and the
half-product operators of completed outcome words.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Left tensor-placement for `\widehat G^x_g`. -/
noncomputable def gHatSelfConsistencyLeftFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) (GHatOutcome params) (ι × ι) :=
  fun x => leftPlacedSubMeas (ιB := ι) ((gHatIdxMeas params family x).toSubMeas)

/-- Right tensor-placement for `\widehat G^x_g`. -/
noncomputable def gHatSelfConsistencyRightFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) (GHatOutcome params) (ι × ι) :=
  fun x => rightPlacedSubMeas (ιA := ι) ((gHatIdxMeas params family x).toSubMeas)

/-- The ordered half-product `\widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k}`. -/
noncomputable def gHatHalfProductOutcomeOperator (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    (k : ℕ) → PointTuple params k → GHatTupleOutcome params k → MIPStarRE.Quantum.Op ι
  | 0, _xs, _gs =>
      1
  | k + 1, xs, gs =>
      ((gHatIdxMeas params family (xs 0)).toSubMeas).outcome (gs 0) *
        gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) (gHatTupleOutcomeTail gs)

/-- The total half-product
`\sum_{g_1,\dots,g_k} \widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k}`. -/
noncomputable def gHatHalfProductTotalOperator (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    (k : ℕ) → PointTuple params k → MIPStarRE.Quantum.Op ι
  | 0, _xs =>
      1
  | k + 1, xs =>
      ((gHatIdxMeas params family (xs 0)).toSubMeas).total *
        gHatHalfProductTotalOperator params family k (pointTupleTail xs)

/-- Splitting a nonempty completed-outcome tuple into its first outcome and tail. -/
def gHatTupleOutcomeConsEquiv' (params : Parameters) [FieldModel params.q] (k : ℕ) :
    GHatTupleOutcome params (k + 1) ≃ GHatOutcome params × GHatTupleOutcome params k where
  toFun gs := (gs 0, gHatTupleOutcomeTail gs)
  invFun p := Fin.cons p.1 p.2
  left_inv gs := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  right_inv p := by
    cases p
    rfl

/-- The total operator of the ordered half-product is always the identity. -/
lemma gHatHalfProductTotalOperator_eq_one (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ k (xs : PointTuple params k), gHatHalfProductTotalOperator params family k xs = 1
  | 0, _xs => by
      simp [gHatHalfProductTotalOperator]
  | k + 1, xs => by
      rw [gHatHalfProductTotalOperator]
      simp [gHatIdxMeas, completeSubMeas,
        gHatHalfProductTotalOperator_eq_one params family k (pointTupleTail xs)]

end MIPStarRE.LDT.Pasting
