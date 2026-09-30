import MIPStarRE.LDT.MainInductionStep.Theorems.PastingAssembly.AnswerFields
import MIPStarRE.LDT.Test.SchwartzZippelStep
import MIPStarRE.LDT.Preliminaries.ComparisonProjective
import MIPStarRE.LDT.Test.StrategyBiProjUnsymmetrization

/-!
# Source-Boundary Role-Register Handoff: Core Reductions

This module contains the main-induction handoff, unsymmetrization, and the first
two-space projectivization outputs for the source route toward `thm:main-formal`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

open MIPStarRE.LDT.MakingMeasurementsProjective

namespace ProjStrat

-- The proof compares two averaged consistency defects after expanding the
-- role-register symmetrization and polynomial-evaluation extraction maps.
/-- Unsymmetrize the two point-consistency estimates obtained from a
role-register source-induction measurement.

Paper origin: `references/ldt-paper/inductive_step.tex:84-109`.

This theorem is the quantitative part of the heterogeneous role-register
reduction before the later projectivization and completion steps.  It starts
from the consistency estimate produced on the role-register symmetrized
strategy and extracts the two occupied principal blocks of the polynomial
measurement.  The factor `2` is exactly the factor coming from the two role
sectors in the symmetrized state.

This statement is source-boundary infrastructure, not a replacement for
`thm:main-formal`: the extracted measurements are complete measurements, not
yet projective measurements, and the error has not yet been absorbed into
`mainFormalError`. -/
theorem sourceRoleRegisterPointConsistency_ofSymConsistency
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (G : Measurement (Polynomial params) (RoleRegisterLocal ιA ιB))
    (σ : Error)
    (hsym :
      ConsRel (strategy.roleRegisterSymmStrategy).state
        (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas (strategy.roleRegisterSymmStrategy).pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        σ) :
    ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
        (polynomialEvaluationFamily params
          (Measurement.extractRoleRegisterBob G).toSubMeas)
        (2 * σ) ∧
      ConsRel strategy.state (uniformDistribution (Point params))
        (polynomialEvaluationFamily params
          (Measurement.extractRoleRegisterAlice G).toSubMeas)
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
        (2 * σ) := by
  haveI : Nonempty ιA := strategy.isNormalized.nonempty.map Prod.fst
  haveI : Nonempty ιB := strategy.isNormalized.nonempty.map Prod.snd
  constructor
  · refine ⟨?_⟩
    have hmono :
        bipartiteConsError strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params
              (Measurement.extractRoleRegisterBob G).toSubMeas)
          ≤
        avgOver (uniformDistribution (Point params)) (fun u =>
          2 * qBipartiteConsDefect (strategy.roleRegisterSymmStrategy).state
            ((IdxProjMeas.toIdxSubMeas
              (strategy.roleRegisterSymmStrategy).pointMeasurement) u)
            ((polynomialEvaluationFamily params G.toSubMeas) u)) := by
      unfold bipartiteConsError
      apply avgOver_mono
      intro u
      let Gu := Test.polynomialEvaluationMeasurementFamily params G u
      have hpoint :=
        qBipartiteConsDefect_extractRoleRegisterBob_le_two_symm
          strategy.state strategy.isNormalized
          (strategy.pointMeasurementA u) (strategy.pointMeasurementB u)
          Gu
      rw [congrFun (polynomialEvaluationFamily_measurement_extractRoleRegisterBob G) u]
      change
        qBipartiteConsDefect strategy.state
            (strategy.pointMeasurementA u).toSubMeas
            (Gu.extractRoleRegisterBob).toSubMeas
          ≤
          2 *
            qBipartiteConsDefect (roleRegisterSymmState strategy.state)
              (roleRegisterProjMeas (strategy.pointMeasurementA u)
                (strategy.pointMeasurementB u)).toSubMeas
              Gu.toSubMeas
      exact hpoint
    have hscale :
        avgOver (uniformDistribution (Point params)) (fun u =>
          2 * qBipartiteConsDefect (strategy.roleRegisterSymmStrategy).state
            ((IdxProjMeas.toIdxSubMeas
              (strategy.roleRegisterSymmStrategy).pointMeasurement) u)
            ((polynomialEvaluationFamily params G.toSubMeas) u))
          =
        2 * bipartiteConsError (strategy.roleRegisterSymmStrategy).state
          (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas (strategy.roleRegisterSymmStrategy).pointMeasurement)
          (polynomialEvaluationFamily params G.toSubMeas) := by
      simp [bipartiteConsError, avgOver_const_mul]
    calc
      bipartiteConsError strategy.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
          (polynomialEvaluationFamily params
            (Measurement.extractRoleRegisterBob G).toSubMeas)
        ≤ avgOver (uniformDistribution (Point params)) (fun u =>
            2 * qBipartiteConsDefect (strategy.roleRegisterSymmStrategy).state
              ((IdxProjMeas.toIdxSubMeas
                (strategy.roleRegisterSymmStrategy).pointMeasurement) u)
              ((polynomialEvaluationFamily params G.toSubMeas) u)) := hmono
      _ = 2 * bipartiteConsError (strategy.roleRegisterSymmStrategy).state
            (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas (strategy.roleRegisterSymmStrategy).pointMeasurement)
            (polynomialEvaluationFamily params G.toSubMeas) := hscale
      _ ≤ 2 * σ := by
            exact mul_le_mul_of_nonneg_left hsym.offDiagonalBound (by norm_num)
  · refine ⟨?_⟩
    have hmono :
        bipartiteConsError strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params
              (Measurement.extractRoleRegisterAlice G).toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
          ≤
        avgOver (uniformDistribution (Point params)) (fun u =>
          2 * qBipartiteConsDefect (strategy.roleRegisterSymmStrategy).state
            ((IdxProjMeas.toIdxSubMeas
              (strategy.roleRegisterSymmStrategy).pointMeasurement) u)
            ((polynomialEvaluationFamily params G.toSubMeas) u)) := by
      unfold bipartiteConsError
      apply avgOver_mono
      intro u
      let Gu := Test.polynomialEvaluationMeasurementFamily params G u
      have hpoint :=
        qBipartiteConsDefect_extractRoleRegisterAlice_le_two_symm
          strategy.state strategy.isNormalized
          (strategy.pointMeasurementA u) (strategy.pointMeasurementB u)
          Gu
      rw [congrFun (polynomialEvaluationFamily_measurement_extractRoleRegisterAlice G) u]
      change
        qBipartiteConsDefect strategy.state
            (Gu.extractRoleRegisterAlice).toSubMeas
            (strategy.pointMeasurementB u).toSubMeas
          ≤
          2 *
            qBipartiteConsDefect (roleRegisterSymmState strategy.state)
              (roleRegisterProjMeas (strategy.pointMeasurementA u)
                (strategy.pointMeasurementB u)).toSubMeas
              Gu.toSubMeas
      exact hpoint
    have hscale :
        avgOver (uniformDistribution (Point params)) (fun u =>
          2 * qBipartiteConsDefect (strategy.roleRegisterSymmStrategy).state
            ((IdxProjMeas.toIdxSubMeas
              (strategy.roleRegisterSymmStrategy).pointMeasurement) u)
            ((polynomialEvaluationFamily params G.toSubMeas) u))
          =
        2 * bipartiteConsError (strategy.roleRegisterSymmStrategy).state
          (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas (strategy.roleRegisterSymmStrategy).pointMeasurement)
          (polynomialEvaluationFamily params G.toSubMeas) := by
      simp [bipartiteConsError, avgOver_const_mul]
    calc
      bipartiteConsError strategy.state (uniformDistribution (Point params))
          (polynomialEvaluationFamily params
            (Measurement.extractRoleRegisterAlice G).toSubMeas)
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
        ≤ avgOver (uniformDistribution (Point params)) (fun u =>
            2 * qBipartiteConsDefect (strategy.roleRegisterSymmStrategy).state
              ((IdxProjMeas.toIdxSubMeas
                (strategy.roleRegisterSymmStrategy).pointMeasurement) u)
              ((polynomialEvaluationFamily params G.toSubMeas) u)) := hmono
      _ = 2 * bipartiteConsError (strategy.roleRegisterSymmStrategy).state
            (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas (strategy.roleRegisterSymmStrategy).pointMeasurement)
            (polynomialEvaluationFamily params G.toSubMeas) := hscale
      _ ≤ 2 * σ := by
            exact mul_le_mul_of_nonneg_left hsym.offDiagonalBound (by norm_num)

/-- Passing the two-space low individual degree test bounds the point-agreement
branch by `3ε`.

It follows because the point-agreement branch is one of the three nonnegative
terms averaged in `ProjStrat.lowIndividualDegreeFailureProbability`. -/
theorem pointAgreementFailureProbability_le_three_mul
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    {strategy : ProjStrat params ιA ιB}
    {eps : Error}
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    strategy.pointAgreementFailureProbability ≤ 3 * eps := by
  have haxis_nonneg : 0 ≤ strategy.axisParallelRoleAverage :=
    axisParallelRoleAverage_nonneg strategy
  have hpoint_nonneg : 0 ≤ strategy.pointAgreementFailureProbability :=
    pointAgreementFailureProbability_nonneg strategy
  have hdiag_nonneg : 0 ≤ strategy.diagonalRoleAverage :=
    diagonalRoleAverage_nonneg strategy
  have hmain :
      (strategy.axisParallelRoleAverage + strategy.pointAgreementFailureProbability +
        strategy.diagonalRoleAverage) / 3 ≤ eps := by
    simpa only [lowIndividualDegreeFailureProbability_eq_role_averages] using
      hpass.soundnessHypothesis
  linarith

/-- The two-space Step 5 self-consistency calculation before projectivization.

Paper origin: `references/ldt-paper/inductive_step.tex:111-133`.

Starting from the two unsymmetrized estimates
`G^A_[g(u)=a] \otimes I \simeq_\sigma I \otimes A^{B,u}_a` and
`A^{A,u}_a \otimes I \simeq_\sigma I \otimes G^B_[g(u)=a]`,
the original point-agreement branch of the test gives the evaluated polynomial
consistency at error `σ + 2 sqrt(3ε + σ)`.  The heterogeneous
Schwartz--Zippel Step 5 lemma then gives full-polynomial consistency with the
additional `md/q` loss. -/
theorem sourceRoleRegisterFullPolynomialSelfConsistency_ofPointConsistency
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps σ : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (G_A : Measurement (Polynomial params) ιA)
    (G_B : Measurement (Polynomial params) ιB)
    (hpointAGB :
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
        (polynomialEvaluationFamily params G_B.toSubMeas)
        σ)
    (hGApointB :
      ConsRel strategy.state (uniformDistribution (Point params))
        (polynomialEvaluationFamily params G_A.toSubMeas)
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
        σ) :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas)
      (σ + 2 * Real.sqrt (3 * eps + σ) +
        (params.m * params.d : Error) / params.q) := by
  let leftEval : IdxMeas (Point params) (Fq params) ιA :=
    Test.polynomialEvaluationMeasurementFamily params G_A
  let rightEval : IdxMeas (Point params) (Fq params) ιB :=
    Test.polynomialEvaluationMeasurementFamily params G_B
  let pointA : IdxMeas (Point params) (Fq params) ιA :=
    IdxProjMeas.toIdxMeas strategy.pointMeasurementA
  let pointB : IdxMeas (Point params) (Fq params) ιB :=
    IdxProjMeas.toIdxMeas strategy.pointMeasurementB
  have hleft : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas leftEval) (IdxMeas.toIdxSubMeas pointB) σ := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params G_A.toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
      σ
    exact hGApointB
  have hpoint : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas pointA) (IdxMeas.toIdxSubMeas pointB) (3 * eps) := by
    refine ⟨?_⟩
    change bipartiteConsError strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) ≤ 3 * eps
    simpa [ProjStrat.pointAgreementFailureProbability] using
      pointAgreementFailureProbability_le_three_mul params hpass
  have hright : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas pointA) (IdxMeas.toIdxSubMeas rightEval) σ := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params G_B.toSubMeas)
      σ
    exact hpointAGB
  have hevaluated : ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params G_A.toSubMeas)
      (polynomialEvaluationFamily params G_B.toSubMeas)
      (σ + 2 * Real.sqrt (3 * eps + σ)) := by
    have htriangle :=
      Preliminaries.simeqTriangleInequality_heterogeneous strategy.state
        (uniformDistribution (Point params)) strategy.isNormalized
        (uniformDistribution_weight_sum_le_one (Point params))
        leftEval pointA pointB rightEval σ (3 * eps) σ hleft hpoint hright
    change ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas leftEval) (IdxMeas.toIdxSubMeas rightEval)
      (σ + 2 * Real.sqrt (3 * eps + σ))
    exact htriangle
  exact
    Test.mainFormalStep5_selfConsistency_ofExpansionBound_heterogeneous params strategy.state
      strategy.isNormalized G_A.toSubMeas G_B.toSubMeas
      (σ + 2 * Real.sqrt (3 * eps + σ)) hevaluated

end ProjStrat

end MIPStarRE.LDT
