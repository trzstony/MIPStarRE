import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization.RestrictSome
import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.ConsistentMeasurements
import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.RightConsistentMeasurements
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.HelperSSC.Assembly
import MIPStarRE.LDT.SelfImprovement.Theorems.AddInUFullStatement
import MIPStarRE.LDT.SelfImprovement.Simplified.VarianceCertificate

/-!
# Self-improvement helper

The helper stage of self-improvement, `lem:self-improvement-helper`: from a
complete polynomial measurement consistent with the point measurements, the
Section 9 semidefinite program produces a filtered sub-measurement with the
four helper conclusions.

## Contents

- **self_improvement_helper_with_slackness** — the slackness-carrying helper
  conclusion from the Section 9 SDP statement.
- **self_improvement_helper_with_contraction** — the same conclusion together
  with the certificate contraction `Z² ≤ H ≤ I` used by dilation.

## References

- `references/ldt-paper/self_improvement.tex`
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Conditional form of the helper lemma from a slackness-carrying SDP
conclusion.

The Section 9 strong-duality conclusion is supplied as
`SdpStatementWithSlackness`.  The helper output therefore carries the
complementary-slackness equations needed by the helper-completeness chain. -/
lemma self_improvement_helper_with_slackness_of_sdp_statement_with_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hsdp : SdpStatementWithSlackness params strategy)
    (hgood : strategy.IsGood eps delta gamma)
    (_nu : Error)
    -- These arguments keep the slackness-carrying conclusion aligned with the
    -- helper theorem; the constructed SDP measurement is independent of `G`.
    (_G : Measurement (Polynomial params) ι) :
    ∃ T : Measurement (Polynomial params) ι,
      ∃ H : SubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
        SelfImprovementHelperConclusionWithSlackness params strategy T H Z eps delta := by
  obtain ⟨T, Z, hsdpPair⟩ := hsdp.witness
  let Hhat : SubMeas (Polynomial params) ι :=
    averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas
  refine ⟨T, Hhat, Z, ?_⟩
  refine
    { toHelperConclusion := ?_
      complementarySlackness := ?_ }
  · refine
      { sdpWitness := ?_
        averagedConstruction := rfl
        addInUVarianceBound := ?_ }
    · exact hsdpPair.toSdpOptimalPair
    · exact addInU (ι := ι) params strategy eps delta gamma hgood T
  · intro g
    exact hsdpPair.complementarySlackness g

/-- Helper lemma driven by the Section 9 SDP statement with complementary
slackness.

This applies the Section 9 statement `sdp_statement_with_slackness`, which
records the strong-duality conclusion with complementary slackness. -/
lemma self_improvement_helper_with_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (nu : Error)
    (G : Measurement (Polynomial params) ι) :
    ∃ T : Measurement (Polynomial params) ι,
      ∃ H : SubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
        SelfImprovementHelperConclusionWithSlackness params strategy T H Z eps delta :=
  self_improvement_helper_with_slackness_of_sdp_statement_with_slackness
    params strategy eps delta gamma
    (sdp_statement_with_slackness (ι := ι) params strategy)
    hgood nu G

/-- Paper origin: `references/ldt-paper/self_improvement.tex:24-60`
(`\label{lem:self-improvement-helper}`).

Self-improvement helper lemma for a polynomial measurement `G` consistent with
the point measurement. It produces a polynomial submeasurement `H` and a
positive contraction `Z` satisfying the four conclusions of the paper:
completeness, consistency with `A`, strong self-consistency, and boundedness.
The boundedness conclusion is split into positivity of `Z`, pointwise domination
of the averaged point measurement, and the state-dependent gap estimate.  The
strong-self-consistency branch is proved in this file and is not exposed as an
additional public hypothesis. The square certificate `Z² ≤ H.total` is
the simplified proof's algebraic input for dilation. -/
lemma self_improvement_helper_with_contraction
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (nu : Error)
    (G : Measurement (Polynomial params) ι)
    (hcons :
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas) nu) :
    ∃ H : SubMeas (Polynomial params) ι,
      ∃ Z : MIPStarRE.Quantum.Op ι,
        SelfImprovementHelperStatement params strategy H Z eps delta nu ∧
          Z ≤ 1 ∧ Z * Z ≤ H.total := by
  rcases self_improvement_helper_with_slackness params strategy eps delta gamma
      hgood nu G with
    ⟨T, Hhat, Z, hhelperWithSlackness⟩
  let hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta :=
    hhelperWithSlackness.toHelperConclusion
  have heps : 0 ≤ eps := eps_nonneg_of_isGood params strategy hgood
  have hdelta : 0 ≤ delta := delta_nonneg_of_isGood params strategy hgood
  have hpointSSC :
      BipartiteSSCRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta := by
    exact ⟨by
      simpa [SymStrat.selfConsistencyFailureProbability] using
        hgood.selfConsistencyTest⟩
  have haddInUFull : AddInUFullStatement params strategy T eps delta :=
    addInUFullStatement_of_isGood (ι := ι) params strategy eps delta gamma hgood T
  have hpointTransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          Hhat
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T.toSubMeas
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta := by
    have htransfer :=
      haddInUFull.selectionDependentTransfer
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (pointConsistencyAddInUSelection params)
    simpa [hhelper.averagedConstruction] using htransfer
  have hcertificate := helper_filtered_certificate_of_slackness
    params strategy T Hhat Z eps delta hhelperWithSlackness
  refine ⟨Hhat, Z, ?_, hcertificate.2.1, hcertificate.2.2.1⟩
  refine
    { completeness := ?_
      pointConsistency := ?_
      strongSelfConsistency := ?_
      positiveSemidefiniteWitness := hhelper.sdpWitness.dualPositive
      dualDominatesAveragedPoint := hhelper.sdpWitness.dualFeasible
      boundednessGap := ?_ }
  · exact
      helper_completeness_of_self_consistency_helper_slackness_input_consistency
        params strategy G eps delta nu heps hdelta hhelperWithSlackness hpointSSC hcons
  · exact
      helper_point_consistency_of_pointConsistencyAddInU_transfer
        params strategy eps delta heps hdelta hpointTransfer
  · by_cases hd_le_q : (params.d : Error) ≤ (params.q : Error)
    · have hlocal :
          (∑ g : Polynomial params,
            localVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g) ≤
            localVarianceOfPointsError params eps delta :=
        localVarianceDeviation_sum_le_localVarianceOfPointsError
          params strategy eps delta gamma hgood T.toSubMeas
      have hclone :
          |helperDeleteAQuantity params strategy T.toSubMeas -
            helperDeleteAClonedQuantity params strategy T.toSubMeas| ≤
              Real.sqrt (selfImprovementVarianceError params eps delta) :=
        helperDeleteAQuantity_abs_sub_clonedQuantity_le_sqrt
          params strategy eps delta T.toSubMeas hlocal
      have hmove :
          |helperDeleteAClonedQuantity params strategy T.toSubMeas -
            helperMoveOverVQuantity params strategy T.toSubMeas| ≤
              Real.sqrt (2 * delta) :=
        helperDeleteAClonedQuantity_abs_sub_moveOverVQuantity_le_sqrt_two_delta
          params strategy delta T.toSubMeas hpointSSC
      have hsscBounds :
          HelperStrongSelfConsistencyBounds params strategy T Hhat eps delta :=
        helper_ssc_bounds_of_scalarTransports_pointTransfer
          params strategy eps delta hhelper hpointSSC hlocal hclone hmove
          (fun h => helper_slackness_eq_of_helper_with_slackness
            params strategy eps delta hhelperWithSlackness h)
          hpointTransfer
      exact
        helper_strong_self_consistency_of_helper_conclusion
          params strategy eps delta heps hdelta hd_le_q hhelper hsscBounds
    · have hhelperError_ge_one : 1 ≤ selfImprovementHelperError params eps delta := by
        have hdq_ge_one : 1 ≤ ((params.d : Error) / (params.q : Error)) := by
          exact (one_le_div₀ params.q_cast_pos).2 (le_of_lt (lt_of_not_ge hd_le_q))
        have hsqrt_dq_ge_one : 1 ≤ Real.sqrt ((params.d : Error) / (params.q : Error)) := by
          have hdq_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) :=
            d_q_ratio_nonneg params
          have hsqrt_nonneg : 0 ≤ Real.sqrt ((params.d : Error) / (params.q : Error)) :=
            Real.sqrt_nonneg _
          have hsq :
              Real.sqrt ((params.d : Error) / (params.q : Error)) *
                Real.sqrt ((params.d : Error) / (params.q : Error)) =
                ((params.d : Error) / (params.q : Error)) := by
            simpa [sq] using Real.sq_sqrt hdq_nonneg
          nlinarith
        have hsqrt_eps_nn : 0 ≤ Real.sqrt eps := Real.sqrt_nonneg _
        have hsqrt_delta_nn : 0 ≤ Real.sqrt delta := Real.sqrt_nonneg _
        rw [selfImprovementHelperError_eq]
        nlinarith [one_le_m_cast params, hsqrt_dq_ge_one, hsqrt_eps_nn, hsqrt_delta_nn]
      have hmatch_nonneg : 0 ≤ qBipartiteMatchMass strategy.state Hhat Hhat := by
        unfold qBipartiteMatchMass
        exact Finset.sum_nonneg fun h _ =>
          ev_nonneg_of_psd strategy.state _ <|
            opTensor_nonneg (Hhat.outcome_pos h) (Hhat.outcome_pos h)
      have hmass_le_one : subMeasMass strategy.state Hhat.liftLeft ≤ 1 := by
        unfold subMeasMass SubMeas.liftLeft
        have hle : leftTensor (ι₂ := ι) Hhat.total ≤
            (1 : MIPStarRE.Quantum.Op (ι × ι)) :=
          leftTensor_le_one (ι₂ := ι) Hhat.total_le_one
        simpa [ev_one_of_isNormalized strategy.state strategy.isNormalized] using
          ev_mono strategy.state _ _ hle
      have hssc_defect_le_one : qBipartiteSSCDefect strategy.state Hhat ≤ 1 := by
        unfold qBipartiteSSCDefect
        have hinner :
            subMeasMass strategy.state Hhat.liftLeft -
                qBipartiteMatchMass strategy.state Hhat Hhat ≤ 1 := by
          linarith
        exact max_le_iff.mpr ⟨by positivity, hinner⟩
      have hssc_le_one :
          bipartiteSSCError strategy.state (uniformDistribution Unit)
            (constSubMeasFamily Hhat) ≤ 1 := by
        simpa [bipartiteSSCError, avgOver, uniformDistribution, constSubMeasFamily] using
          hssc_defect_le_one
      exact ⟨le_trans hssc_le_one hhelperError_ge_one⟩
  · exact
      helper_boundedness_gap_le_selfImprovementHelperError_of_helper_outputs
        params strategy eps delta heps hdelta hhelper hpointSSC
        (fun h => (hhelperWithSlackness.complementarySlackness h).symm)
        hpointTransfer

end MIPStarRE.LDT.SelfImprovement
