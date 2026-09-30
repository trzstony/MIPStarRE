import MIPStarRE.LDT.Test.Defs
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerIdentities.PositiveGram.Sigma
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.BoundednessTransport.Decomposition

/-!
# Boundedness transport point-consistency estimates

This file contains the point-consistency consequences of the helper-agreement
off-diagonal decomposition and the natural-error transports through the final
projective fields.

## References

- `references/ldt-paper/self_improvement.tex` lines 435 and 747--755
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.Quantum
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The tensor product with the identity on the left register is the right tensor
placement. -/
lemma opTensor_one_left_eq_rightTensor
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (B : MIPStarRE.Quantum.Op ι₂) :
    opTensor (ι₁ := ι₁) (1 : MIPStarRE.Quantum.Op ι₁) B =
      rightTensor (ι₁ := ι₁) B := by
  rfl

/-- The point measurement is complete and polynomial evaluation preserves the
right-register total, so the tensor total has the same expectation as the right
placement of the original total. -/
lemma pointMeasurement_total_evalFamily_total_opTensor_ev_eq_rightTensor
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (S : SubMeas (Polynomial params) ι)
    (u : Point params) :
    ev strategy.state
        (opTensor
          (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total)
          (((polynomialEvaluationFamily params S) u).total)) =
      ev strategy.state (rightTensor (ι₁ := ι) S.total) := by
  have hA_total :
      (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) =
        (1 : MIPStarRE.Quantum.Op ι) := by
    exact (strategy.pointMeasurement u).total_eq_one
  have hS_total : (((polynomialEvaluationFamily params S) u).total) = S.total := by
    simpa [polynomialEvaluationFamily, evaluateAt] using
      postprocess_total S (fun g : Polynomial params => g u)
  rw [hA_total, hS_total, opTensor_one_left_eq_rightTensor]

/-- The helper-stage consistency defect is exactly the averaged off-diagonal
mass appearing in the point-consistency `add-in-u` calculation.

This is the same algebraic identity as
`helper_boundedness_slack_average_ev_eq_off_diagonal_avg`, read as a
`ConsRel` defect for the point measurement against the polynomial-evaluation
family of `H`. -/
theorem helper_point_consistency_error_eq_off_diagonal_avg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι) :
    bipartiteConsError strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (H.outcome h))) := by
  classical
  unfold bipartiteConsError
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  have hdiff_eq :
      ev strategy.state (rightTensor (ι₁ := ι) H.total) -
          ev strategy.state (helperAgreementOperatorAtPoint params strategy H u) =
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (H.outcome h)) := by
    exact helperAgreementOperatorAtPoint_ev_slack_eq_off_diagonal_sum params strategy H u
  have hdiff_nonneg :
      0 ≤ ev strategy.state (rightTensor (ι₁ := ι) H.total) -
          ev strategy.state (helperAgreementOperatorAtPoint params strategy H u) := by
    rw [hdiff_eq]
    exact Finset.sum_nonneg fun h _ =>
      Finset.sum_nonneg fun a _ =>
        ev_nonneg_of_psd strategy.state _
          (opTensor_nonneg ((strategy.pointMeasurement u).toMeasurement.outcome_pos a)
            (H.outcome_pos h))
  have htotal :
      ev strategy.state
          (opTensor
            (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total)
            (((polynomialEvaluationFamily params H) u).total)) =
        ev strategy.state (rightTensor (ι₁ := ι) H.total) := by
    exact pointMeasurement_total_evalFamily_total_opTensor_ev_eq_rightTensor
      params strategy H u
  have hmatch :
      qBipartiteMatchMass strategy.state
          ((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u)
          ((polynomialEvaluationFamily params H) u) =
        ev strategy.state (helperAgreementOperatorAtPoint params strategy H u) := by
    simp [qBipartiteMatchMass, helperAgreementOperatorAtPoint,
      polynomialEvaluationFamily, evaluateAt, ev_sum, IdxProjMeas.toIdxSubMeas]
  unfold qBipartiteConsDefect
  rw [htotal, hmatch]
  rw [max_eq_right hdiff_nonneg, hdiff_eq]

-- This point-consistency conversion expands the off-diagonal add-in-u transfer
-- and the helper error normalization.
/-- Helper-stage point consistency from the point-consistency `add-in-u`
transfer hypothesis.

The transfer bound controls the off-diagonal mass
`E_u ∑_h ∑_{a ≠ h(u)} ⟨ψ, A^u_a ⊗ Hhat_h ψ⟩`.  The preceding algebraic
identity identifies this mass with the `ConsRel` defect for the point
measurement and the polynomial-evaluation family of `Hhat`. -/
theorem helper_point_consistency_of_pointConsistencyAddInU_transfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T Hhat : SubMeas (Polynomial params) ι}
    (htransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          Hhat
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params Hhat)
      (selfImprovementHelperError params eps delta) := by
  refine ⟨?_⟩
  rw [helper_point_consistency_error_eq_off_diagonal_avg]
  exact
    pointConsistencyAddInU_off_diagonal_avg_le_helper_error_of_transfer
      params strategy eps delta heps hdelta T Hhat htransfer

-- This lemma composes the selected point-consistency add-in-u chain with the
-- point-consistency conversion above.

end MIPStarRE.LDT.SelfImprovement
