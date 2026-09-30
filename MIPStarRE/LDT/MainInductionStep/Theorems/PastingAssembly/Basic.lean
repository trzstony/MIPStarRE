import MIPStarRE.LDT.MainInductionStep.Theorems.RestrictedProbabilities.AnswerValued
import MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds.Averaging
import MIPStarRE.LDT.CommutativityPoints.AnswerTheorems

/-!
# Section 6 — Pasting Assembly: Averaged Family Fields

This module contains the scalar preliminary bound and the averaged family-field
lemmas used by the answer-valued successor route.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- The mass of the averaged polynomial family is the average of the masses of
the slice measurements.

This is the linearity calculation underlying the completeness part of the
averaged pasting assembly. -/
lemma idxPolyFamily_averagedMass_eq_avg
    (params : Parameters)
    [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) :
    subMeasMass ψ family.averagedSubMeas.liftLeft =
      avgOver (uniformDistribution (Fq params))
        (fun x => subMeasMass ψ ((family.meas x).toSubMeas.liftLeft)) := by
  simp only [subMeasMass, IdxPolyFamily.averagedSubMeas, SubMeas.liftLeft,
    mkLeftPlacedSubMeas_total, averageIdxSubMeas]
  exact ev_leftTensor_averageOperatorOverDistribution ψ (uniformDistribution (Fq params))
    (fun x => (family.meas x).toSubMeas.total)

/-- Averaged completeness of a slice-indexed polynomial family from pointwise
slice completeness.

This is the completeness component of the Section 6 averaging argument.  The
statement is family-level: it does not mention diagonal measurements, and hence
can be reused in the answer-valued successor route. -/
lemma idxPolyFamily_complete_of_slice_bounds
    (params : Parameters)
    [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (sliceError sliceSelfError : Fq params → Error)
    (hcomplete :
      ∀ x,
        CompletenessAtLeast ψ ((family.meas x).toSubMeas.liftLeft)
          ((1 - sliceError x) - sliceSelfError x)) :
    family.Complete ψ
      (avgOver (uniformDistribution (Fq params)) sliceError +
        avgOver (uniformDistribution (Fq params)) sliceSelfError) := by
  classical
  let 𝒟 : Distribution (Fq params) := uniformDistribution (Fq params)
  refine ⟨?_⟩
  refine ⟨?_⟩
  have hmass_eq := idxPolyFamily_averagedMass_eq_avg params ψ family
  have havg_lower :
      1 - (avgOver 𝒟 sliceError + avgOver 𝒟 sliceSelfError) ≤
        avgOver 𝒟
          (fun x => subMeasMass ψ ((family.meas x).toSubMeas.liftLeft)) := by
    have hconst1 : avgOver 𝒟 (fun _ : Fq params => (1 : Error)) = 1 := by
      simpa [𝒟] using (avgOver_uniform_const (α := Fq params) (1 : Error))
    have hnegErr : avgOver 𝒟 (fun a => -sliceError a) = -avgOver 𝒟 sliceError := by
      simpa [avgOver_const_mul] using (avgOver_const_mul 𝒟 (-1) sliceError)
    have hnegZeta :
        avgOver 𝒟 (fun a => -sliceSelfError a) = -avgOver 𝒟 sliceSelfError := by
      simpa [avgOver_const_mul] using (avgOver_const_mul 𝒟 (-1) sliceSelfError)
    calc
      1 - (avgOver 𝒟 sliceError + avgOver 𝒟 sliceSelfError) =
          avgOver 𝒟 (fun x => (1 - sliceError x) - sliceSelfError x) := by
            rw [show (fun x => (1 - sliceError x) - sliceSelfError x) =
                fun x => 1 + (-sliceError x) + (-sliceSelfError x) by
                funext x
                ring]
            rw [avgOver_add, avgOver_add, hconst1, hnegErr, hnegZeta]
            ring
      _ ≤ avgOver 𝒟
          (fun x => subMeasMass ψ ((family.meas x).toSubMeas.liftLeft)) := by
            apply avgOver_mono
            intro x
            exact (hcomplete x).lowerBound
  rw [hmass_eq]
  exact havg_lower

/-- Point-consistency averaging for answer-valued restricted slices of an
ordinary ambient successor strategy. -/
lemma family_answerRestrictedPointConsistencyError_eq_avg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) :
    bipartiteConsError strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxPolyFamily.evaluatedAtNextPoint family) =
      avgOver (uniformDistribution (Fq params))
        (fun x =>
          bipartiteConsError strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas
              (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params (family.meas x).toSubMeas)) := by
  let g : Point params.next → Error := fun u =>
    qBipartiteConsDefect strategy.state
      ((strategy.pointMeasurement u).toSubMeas)
      ((IdxPolyFamily.evaluatedAtNextPoint family) u)
  calc
    bipartiteConsError strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxPolyFamily.evaluatedAtNextPoint family)
      = avgOver (uniformDistribution (Point params.next)) g := by
          rfl
    _ = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Point params))
            (fun u => g (appendPoint params u x))) := by
          exact CommutativityPoints.avgOver_uniform_pointNext_decompose params g
    _ = avgOver (uniformDistribution (Fq params))
          (fun x =>
            bipartiteConsError strategy.state (uniformDistribution (Point params))
              (IdxProjMeas.toIdxSubMeas
                (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
              (polynomialEvaluationFamily params (family.meas x).toSubMeas)) := by
          unfold bipartiteConsError
          avg_congr with x, u
          simp [g, IdxPolyFamily.evaluatedAtNextPoint, polynomialEvaluationFamily,
            IdxProjMeas.toIdxSubMeas, xRestrictedAnswerSymStrat]
          rfl

/-- Average slice-wise left/right closeness into strong self-consistency of the
slice-indexed family.

This is the strong self-consistency component of the Section 6 averaging
argument.  It depends only on the state and the slice measurements, not on the
diagonal part of a strategy. -/
lemma idxPolyFamily_stronglySelfConsistent_of_slice_bounds
    (params : Parameters)
    [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (sliceError : Fq params → Error)
    (zeta : Error)
    (hself :
      ∀ x,
        SDDRel ψ (uniformDistribution Unit)
          (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) (family.meas x).toSubMeas))
          (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) (family.meas x).toSubMeas))
          (sliceError x))
    (havg : avgOver (uniformDistribution (Fq params)) sliceError ≤ zeta) :
    family.StronglySelfConsistent ψ zeta := by
  refine ⟨?_⟩
  refine ⟨?_⟩
  have hpointwise :
      ∀ x,
        qSDD ψ ((family.meas x).toSubMeas.liftLeft)
          ((family.meas x).toSubMeas.liftRight) ≤ sliceError x := by
    intro x
    simpa [sddError, avgOver_uniform_const, constSubMeasFamily,
      SubMeas.liftLeft, SubMeas.liftRight, leftPlacedSubMeas, rightPlacedSubMeas] using
      (hself x).squaredDistanceBound
  calc
    sddError ψ (uniformDistribution (Fq params))
        (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas))
        (IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas))
      = avgOver (uniformDistribution (Fq params))
          (fun x =>
            qSDD ψ ((family.meas x).toSubMeas.liftLeft)
              ((family.meas x).toSubMeas.liftRight)) := by
            rfl
    _ ≤ avgOver (uniformDistribution (Fq params)) sliceError := by
          exact avgOver_mono (uniformDistribution (Fq params)) _ _ hpointwise
    _ ≤ zeta := havg

/-- Average slice-wise boundedness into the boundedness input used by the
induction-section pasting theorem.

This is the boundedness component of the Section 6 averaging argument for an
ordinary successor strategy.  The hypotheses are exactly the slice-wise
residual estimate and the paper domination condition
`E_u A^{u,x}_{g(u)} <= Z^x`.

**Lean-only:** This is an internal adapter for the induction-section pasting
interface, tracked in issue #1507.  Paper origin:
`references/ldt-paper/inductive_step.tex:461-551`.  Discharge: proved here by
averaging the slice-wise boundedness estimates and the domination condition. -/
lemma idxPolyFamily_sliceBoundednessInput_of_slice_bounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (sliceError : Fq params → Error)
    (zeta : Error)
    (hbounded :
      ∀ x,
        tensorFailureExpectation strategy.state (family.witness x)
          (family.meas x).toSubMeas ≤ sliceError x)
    (havg : avgOver (uniformDistribution (Fq params)) sliceError ≤ zeta)
    (hdom :
      ∀ x, ∀ g : Polynomial params,
        IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g ≤ family.witness x) :
    IdxPolyFamily.SliceBoundednessInput strategy family zeta := by
  classical
  refine
    { sliceOpPSD := ?_
      sliceBoundedness := ?_
      sliceDominatesAveragedPoint := hdom }
  · intro x
    let g0 : Polynomial params :=
      Classical.choice (inferInstance : Nonempty (Polynomial params))
    have htarget_nonneg :
        0 ≤ IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g0 := by
      unfold IdxPolyFamily.averagedSlicePointEvaluationOperator
      exact Finset.sum_nonneg fun u hu =>
        smul_nonneg ((uniformDistribution (Point params)).nonnegative u)
          ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome_pos (g0 u))
    exact le_trans htarget_nonneg (hdom x g0)
  · have hswap :
        avgOver (uniformDistribution (Fq params))
            (fun x =>
              ev strategy.state
                (leftTensor (ι₂ := ι) (1 - (family.meas x).toSubMeas.total) *
                  rightTensor (ι₁ := ι) (family.witness x))) =
          avgOver (uniformDistribution (Fq params))
            (fun x =>
              tensorFailureExpectation strategy.state (family.witness x)
                (family.meas x).toSubMeas) := by
      apply avgOver_congr
      intro x
      simpa [tensorFailureExpectation, leftTensor_mul_rightTensor_eq_opTensor] using
        (ev_opTensor_swap_of_density_fixed strategy.state
          strategy.permInvState.density_swap
          (1 - (family.meas x).toSubMeas.total) (family.witness x))
    rw [hswap]
    calc
      avgOver (uniformDistribution (Fq params))
          (fun x =>
            tensorFailureExpectation strategy.state (family.witness x)
              (family.meas x).toSubMeas)
        ≤ avgOver (uniformDistribution (Fq params)) sliceError := by
            exact avgOver_mono (uniformDistribution (Fq params)) _ _ hbounded
      _ ≤ zeta := havg

end MIPStarRE.LDT.MainInductionStep
