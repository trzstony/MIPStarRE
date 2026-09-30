import MIPStarRE.LDT.GlobalVariance.Defs.Core
import MIPStarRE.LDT.Test.StrategyCore

/-!
# Section 10 — Definitions

Auxiliary definitions for the commutativity-at-points argument from Section 10 of the
low individual degree paper. This file packages the sampled diagonal-line questions,
point/line bridge families, and the error terms used by `thm:commutativity-points`.

## References

- `references/ldt-paper/commutativity-points.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)
open scoped BigOperators MatrixOrder ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Outcomes `(a, b)` for the ordered or reversed product of two point measurements. -/
abbrev PointPairOutcome (params : Parameters) := Fq params × Fq params

/-- A diagonal line together with a sampled parameter on that line. -/
abbrev PointDiagonalLineQuestion (params : Parameters) := DiagonalLine params × Fq params

/-- A diagonal line together with the two sampled parameters used for a point pair. -/
abbrev PointPairDiagonalLineQuestion (params : Parameters) :=
  DiagonalLine params × (Fq params × Fq params)

-- leftPlacedSubMeas / rightPlacedSubMeas are defined in Basic/SubMeasurementFamilies.lean

/-- Diagonal lines form a finite type via their base point and direction vector. -/
noncomputable instance (params : Parameters) : Fintype (DiagonalLine params) :=
  Fintype.ofInjective
    (fun ℓ : DiagonalLine params => (ℓ.base, ℓ.direction))
    fun _ _ h => congrArg₂ DiagonalLine.mk (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- Ordered product of two submeasurements viewed as a raw operator family. -/
noncomputable def orderedProductOpFamily {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι) :
    OpFamily (α × β) ι where
  outcome := fun | (a, b) => A.outcome a * B.outcome b
  total := A.total * B.total

/-- Reversed product of two submeasurements viewed as a raw operator family. -/
noncomputable def reversedProductOpFamily {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι) :
    OpFamily (α × β) ι where
  outcome := fun | (a, b) => B.outcome b * A.outcome a
  total := B.total * A.total

/-- The outcome effects of `tensorProductSubMeas` sum to its total effect. -/
theorem tensorProductSubMeas_sum_outcome {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι) :
    ∑ ab : α × β,
        leftTensor (ι₂ := ι) (A.outcome ab.1) * rightTensor (ι₁ := ι) (B.outcome ab.2) =
      leftTensor (ι₂ := ι) A.total * rightTensor (ι₁ := ι) B.total := by
  calc
    ∑ ab : α × β,
        leftTensor (ι₂ := ι) (A.outcome ab.1) * rightTensor (ι₁ := ι) (B.outcome ab.2)
        = ∑ a : α,
            ∑ b : β,
              leftTensor (ι₂ := ι) (A.outcome a) *
                rightTensor (ι₁ := ι) (B.outcome b) := by
                simpa using
                  (Fintype.sum_prod_type' (f := fun a b =>
                    leftTensor (ι₂ := ι) (A.outcome a) *
                      rightTensor (ι₁ := ι) (B.outcome b)))
    _ =
        (∑ a : α, leftTensor (ι₂ := ι) (A.outcome a)) *
          ∑ b : β, rightTensor (ι₁ := ι) (B.outcome b) := by
            rw [← Fintype.sum_mul_sum]
    _ = leftTensor (ι₂ := ι) A.total * rightTensor (ι₁ := ι) B.total := by
          rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ A.outcome]
          rw [rightTensor_finset_sum (ι₁ := ι) Finset.univ B.outcome]
          rw [A.sum_eq_total, B.sum_eq_total]

/-- Tensor-product bridge `A_a ⊗ B_b` on the bipartite space `ι × ι`. -/
noncomputable def tensorProductSubMeas {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι) :
    SubMeas (α × β) (ι × ι) where
  outcome := fun ab =>
    match ab with
    | (a, b) =>
        leftTensor (ι₂ := ι) (A.outcome a) *
          rightTensor (ι₁ := ι) (B.outcome b)
  total := leftTensor (ι₂ := ι) A.total *
             rightTensor (ι₁ := ι) B.total
  outcome_pos := fun ab =>
    (opTensor_nonneg (A.outcome_pos ab.1) (B.outcome_pos ab.2)).trans_eq
      (leftTensor_mul_rightTensor_eq_opTensor (A.outcome ab.1) (B.outcome ab.2)).symm
  sum_eq_total := tensorProductSubMeas_sum_outcome A B
  total_le_one :=
    (leftTensor_mul_rightTensor_eq_opTensor A.total B.total).trans_le
      ((opTensor_le_leftTensor (SubMeas.total_nonneg A) B.total_le_one).trans
        (leftTensor_le_one (ι₂ := ι) A.total_le_one))

/-- Recover the sampled point from a diagonal-line/parameter sample. -/
def sampledPointFromDiagonalQuestion (params : Parameters)
    [FieldModel params.q]
    (q : PointDiagonalLineQuestion params) : Point params :=
  q.1.pointAt q.2

/-- Recover the two sampled points from a shared diagonal-line sample. -/
def sampledPointPairFromSharedDiagonalQuestion (params : Parameters)
    [FieldModel params.q]
    (q : PointPairDiagonalLineQuestion params) : PointPairQuestion params :=
  (q.1.pointAt q.2.1, q.1.pointAt q.2.2)

/-- The ordered point product `(A^u_a A^v_b) ⊗ I` on the bipartite space `d * d`. -/
noncomputable def pointMeasurementProductLeft (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    IdxOpFamily (PointPairQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun uv =>
    let Au := (strategy.pointMeasurement uv.1).toSubMeas
    let Av := (strategy.pointMeasurement uv.2).toSubMeas
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      orderedProductOpFamily Au Av

/-- The reversed point product `(A^v_b A^u_a) ⊗ I` on the bipartite space `ι × ι`. -/
noncomputable def pointMeasurementProductRight (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    IdxOpFamily (PointPairQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun uv =>
    let Au := (strategy.pointMeasurement uv.1).toSubMeas
    let Av := (strategy.pointMeasurement uv.2).toSubMeas
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      reversedProductOpFamily Au Av

/-- Distribution obtained by sampling a diagonal line together with a parameter on that line. -/
noncomputable def pointWithDiagonalLineDistribution (params : Parameters)
    [FieldModel params.q] :
    Distribution (PointDiagonalLineQuestion params) :=
  uniformDistribution (PointDiagonalLineQuestion params)

/-- Realize a shared-line sample from a uniformly random point pair and parameter.

The resulting line is parameterized so that the first point is visited at `t` and the
second at `t + 1`. This matches the paper's sampling of two random points together with
some diagonal line containing both. -/
noncomputable def sharedDiagonalLineQuestionOfPointPair (params : Parameters)
    [FieldModel params.q]
    (s : PointPairQuestion params × Fq params) :
    PointPairDiagonalLineQuestion params :=
  let u := s.1.1
  let v := s.1.2
  let t := s.2
  let direction : Point params := fun i => subCoord (v i) (u i)
  let base : Point params := fun i => subCoord (u i) (mulCoord t (direction i))
  ({ base := base, direction := direction }, (t, addCoord t (encodeScalar 1)))

/-- Distribution obtained by sampling a uniform point pair and then packaging it as a
shared diagonal-line question. -/
noncomputable def pointPairSharedDiagonalLineDistribution (params : Parameters)
    [FieldModel params.q] :
    Distribution (PointPairDiagonalLineQuestion params) :=
  (uniformDistribution (PointPairQuestion params × Fq params)).map
    (sharedDiagonalLineQuestionOfPointPair params)

/-- The intermediate consistency loss coming from the `m`-restricted diagonal-lines test. -/
def restrictedDiagonalLinesConsistencyError (params : Parameters) (gamma : Error) : Error :=
  gamma * (params.m : Error)

/-- The approximation loss obtained from `prop:simeq-to-approx`. -/
def pointDiagonalLineApproxError (params : Parameters) (gamma : Error) : Error :=
  2 * restrictedDiagonalLinesConsistencyError params gamma

/-- The displayed commutativity error from `thm:commutativity-points`. -/
def commutativityPointsError (params : Parameters) (gamma : Error) : Error :=
  32 * gamma * (params.m : Error)

end MIPStarRE.LDT.CommutativityPoints
