import MIPStarRE.LDT.Test.StrategyCore

/-!
# Polynomial-family interfaces for the low individual degree test

Packaged slice-indexed polynomial-family interfaces extracted from
`MIPStarRE.LDT.Test.Strategy`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

/-! ### Polynomial-family interfaces -/

/-- A packaged family `x ↦ G^x` together with its witness operators and domination targets.

The `witness` and `dominationTarget` fields store the per-slice PSD operator
`Z^x` and per-slice, per-polynomial operator `E_u A^{u,x}_{g(u)}` appearing in
the paper's boundedness hypothesis (`references/ldt-paper/commutativity-G.tex`,
item `data-processed-boundedness`). We store these operators explicitly rather
than hiding them behind ambient defaults, so each constructor must choose an
honest witness/target pair.

Callers without access to an ambient strategy can use `ofSliceMeas`, which takes
`Z^x := ∑_g G^x_g` and `dominationTarget x g := G^x_g`. Callers with access to a
symmetric strategy should prefer the constructor `ofSymStrat`,
which derives both fields from the strategy itself. -/
structure IdxPolyFamily (params : Parameters) [FieldModel params.q]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  meas : IdxProjSubMeas (Fq params) (Polynomial params) ι
  witness : Fq params → MIPStarRE.Quantum.Op ι
  dominationTarget : Fq params → Polynomial params → MIPStarRE.Quantum.Op ι

-- NOTE: no global `Inhabited` instance for `IdxPolyFamily`; without an actual
-- slice family, any default would be a degenerate zero-family placeholder.

namespace IdxPolyFamily

/-- The averaged submeasurement `G = E_x G^x`: average the slice
measurements over the uniform distribution on slice heights `x ∈ F_q`. -/
noncomputable def averagedSubMeas {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι) :
    SubMeas (Polynomial params) ι :=
  averageIdxSubMeas (uniformDistribution (Fq params))
    (fun x => (family.meas x).toSubMeas)
    (uniformDistribution_weight_sum_le_one (Fq params))

/-- Evaluate the slice family at a point `(u, x)` in `F_q^{m+1}`. -/
noncomputable def evaluatedAtNextPoint {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (Point params.next) (Fq params) ι :=
  fun u =>
    evaluateAt params (truncatePoint params u)
      ((family.meas (pointHeight params u)).toSubMeas)

/-- Averaged point operator `E_u A^u_{h(u)}` appearing in source-style
boundedness assumptions. -/
noncomputable def averagedPointEvaluationOperator {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) (h : Polynomial params) :
    MIPStarRE.Quantum.Op ι :=
  averageOperatorOverDistribution (uniformDistribution (Point params))
    (fun u => (strategy.pointMeasurement u).toSubMeas.outcome (h u))

/-- Slice-wise averaged point operator `E_u A^{u,x}_{g(u)}` from the paper's
boundedness hypothesis. -/
noncomputable def averagedSlicePointEvaluationOperator {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (x : Fq params) (g : Polynomial params) : MIPStarRE.Quantum.Op ι :=
  averageOperatorOverDistribution (uniformDistribution (Point params))
    (fun u => (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome (g u))

structure Complete {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι)
    (ψ : QuantumState (ι × ι)) (kappa : Error) : Prop where
  averageCompleteness :
    CompletenessAtLeast ψ family.averagedSubMeas.liftLeft (1 - kappa)

structure ConsistentWithPoints {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι)
    (strategy : SymStrat params.next ι) (zeta : Error) : Prop where
  pointConsistency :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      family.evaluatedAtNextPoint
      zeta

/-- A family point-consistency witness forces the displayed point-consistency
error parameter `ζ` to be nonnegative. -/
theorem zeta_nonneg_of_consistentWithPoints {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {zeta : Error}
    (hcons : family.ConsistentWithPoints strategy zeta) :
    0 ≤ zeta := by
  exact le_trans
    (bipartiteConsError_nonneg strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      family.evaluatedAtNextPoint)
    hcons.pointConsistency.offDiagonalBound

structure StronglySelfConsistent {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι)
    (ψ : QuantumState (ι × ι)) (zeta : Error) : Prop where
  sliceSelfConsistency :
    SDDRel ψ (uniformDistribution (Fq params))
      (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas))
      (IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas))
      zeta

/-- Paper-faithful boundedness input for slice-indexed polynomial families.

This structure encodes the boundedness item in
`references/ldt-paper/commutativity-G.tex` and `references/ldt-paper/ld-pasting.tex`.
It consists of positive witnesses `Z^x`, the averaged residual bound
`E_x <psi| (I - G^x) tensor Z^x |psi> <= zeta`, and the domination condition
`Z^x >= E_u A^{u,x}_{g(u)}`.

The domination condition is stated directly against the averaged point operator
from the strategy.  It is not mediated through `family.dominationTarget`, so this
public input does not contain an additional identification bridge. -/
structure SliceBoundednessInput {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (zeta : Error) : Prop where
  /-- Positivity of the slice witnesses `Z^x`. -/
  sliceOpPSD : ∀ x, 0 ≤ family.witness x
  /-- Averaged residual bound `E_x <psi| (I - G^x) tensor Z^x |psi> <= zeta`. -/
  sliceBoundedness :
    avgOver (uniformDistribution (Fq params))
      (fun x =>
        ev strategy.state <|
          leftTensor (ι₂ := ι) (1 - (family.meas x).toSubMeas.total) *
            rightTensor (ι₁ := ι) (family.witness x)) ≤ zeta
  /-- Paper domination condition `E_u A^{u,x}_{g(u)} <= Z^x`. -/
  sliceDominatesAveragedPoint :
    ∀ x : Fq params, ∀ g : Polynomial params,
      averagedSlicePointEvaluationOperator strategy x g ≤ family.witness x

namespace SliceBoundednessInput

/-- The boundedness residual obtained from a concrete slice family `G`.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551`
(`\label{thm:self-improvement-in-induction-section}`), especially the boundedness
field of the slice-wise self-improvement output.

This is the induction-oriented `Z^x ⊗ (I - G^x)` term after replacing the
abstract slice family by the concrete `G`, written in the paper's
`(I - G^x) ⊗ Z^x` orientation. -/
noncomputable def storedResidual {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SymStrat params.next ι}
    {family : IdxPolyFamily params ι} {zeta : Error}
    (_hbound : SliceBoundednessInput strategy family zeta)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (x : Fq params) : Error :=
  ev strategy.state
    (leftTensor (ι₂ := ι) (1 - (G x).total) *
      rightTensor (ι₁ := ι) (family.witness x))

/-- Stored residual half of the boundedness hypothesis.

This is exactly the paper's `(I-G^x) ⊗ Z^x` residual bound from
`references/ldt-paper/commutativity-G.tex`. -/
theorem storedBoundedResidualBound {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SymStrat params.next ι}
    {family : IdxPolyFamily params ι} {zeta : Error}
    (hbound : SliceBoundednessInput strategy family zeta)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas) :
    avgOver (uniformDistribution (Fq params))
      (fun x => hbound.storedResidual G x) ≤ zeta := by
  simpa [storedResidual, hG] using hbound.sliceBoundedness

/-- Paper-faithful domination half of the boundedness hypothesis.

This is the line `Z^x ≥ E_u A^{u,x}_{g(u)}` from
`references/ldt-paper/commutativity-G.tex`. -/
theorem averagedPoint_le_witness {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SymStrat params.next ι}
    {family : IdxPolyFamily params ι} {zeta : Error}
    (hbound : SliceBoundednessInput strategy family zeta) :
    ∀ x : Fq params, ∀ g : Polynomial params,
      averagedSlicePointEvaluationOperator strategy x g ≤ family.witness x :=
  hbound.sliceDominatesAveragedPoint

end SliceBoundednessInput

end IdxPolyFamily

end MIPStarRE.LDT
