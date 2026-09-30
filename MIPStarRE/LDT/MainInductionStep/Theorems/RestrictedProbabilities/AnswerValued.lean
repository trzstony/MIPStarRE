import MIPStarRE.LDT.MainInductionStep.Theorems.RestrictedProbabilities.Axis
import MIPStarRE.LDT.MainInductionStep.Theorems.SelfImprovementAssembly.AnswerSlice
import MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds.Preliminaries

/-!
# Section 6 -- Answer-Valued Restricted Probability Statement

This module contains the answer-valued form of the restricted-probability
bookkeeping for the main induction step.

## References

- `blueprint/src/chapter/ch10_induction.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

universe uF uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- The answer-valued slice has the same axis-parallel failure probability as the
legacy restricted slice. -/
lemma answerRestricted_axisParallelFailureProbability_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability =
      (xRestrictedStrategy params strategy x).axisParallelFailureProbability := by
  rfl

/-- The answer-valued slice has the same self-consistency failure probability as
the legacy restricted slice. -/
lemma answerRestricted_selfConsistencyFailureProbability_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    (xRestrictedAnswerSymStrat params strategy x).selfConsistencyFailureProbability =
      (xRestrictedStrategy params strategy x).selfConsistencyFailureProbability := by
  rfl

/-- The weighted average of the answer-valued restricted axis-parallel slice errors
is bounded by the ambient axis-parallel test error. -/
lemma answer_weighted_axisParallel_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability) ≤
      eps := by
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedStrategy params strategy x).axisParallelFailureProbability) := by
            refine avgOver_congr _ _ _ ?_
            intro x
            rw [answerRestricted_axisParallelFailureProbability_eq]
    _ ≤ eps := weighted_axisParallel_bound params strategy eps delta gamma hgood

/-! ### Answer-valued successor restrictions

The preceding lemmas start from an ordinary successor strategy and build the
answer-valued slice profile used in the current Section 6 successor route.  For
the simultaneous answer-valued induction theorem, the successor strategy itself
has answer-valued diagonal measurements.  The next definitions and lemmas
record the corresponding restricted-probability theorem without replacing that
diagonal measurement by an ordinary low-degree realization.
-/

/-- Slice-wise error profile obtained by restricting an answer-valued successor
strategy.

This is the answer-valued analogue of `AnswerRestrictedFailureProfile`, but
with source strategy `AnswerSymStrat params.next ι` and slices
`xRestrictedAnswerSymStratOfAnswer`. -/
structure AnswerSuccessorRestrictedFailureProfile (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι) : Type where
  /-- The axis-parallel failure bound attached to each slice height. -/
  axisParallel : Fq params → Error
  /-- The self-consistency failure bound attached to each slice height. -/
  selfConsistency : Fq params → Error
  /-- The diagonal-line failure bound attached to each slice height. -/
  diagonal : Fq params → Error
  /-- Each answer-valued slice is good with the recorded parameters. -/
  restrictedGood :
    ∀ x,
      (xRestrictedAnswerSymStratOfAnswer params strategy x).IsGood
        (axisParallel x)
        (selfConsistency x)
        (diagonal x)

/-- Average restricted axis-parallel error over answer-valued successor slices. -/
noncomputable def averageAnswerSuccessorRestrictedAxisParallelError
    (params : Parameters)
    [FieldModel params.q]
    {strategy : AnswerSymStrat params.next ι}
    (profile : AnswerSuccessorRestrictedFailureProfile params strategy) : Error :=
  avgOver (uniformDistribution (Fq params)) profile.axisParallel

/-- Average restricted self-consistency error over answer-valued successor slices. -/
noncomputable def averageAnswerSuccessorRestrictedSelfConsistencyError
    (params : Parameters)
    [FieldModel params.q]
    {strategy : AnswerSymStrat params.next ι}
    (profile : AnswerSuccessorRestrictedFailureProfile params strategy) : Error :=
  avgOver (uniformDistribution (Fq params)) profile.selfConsistency

/-- Average restricted diagonal-line error over answer-valued successor slices. -/
noncomputable def averageAnswerSuccessorRestrictedDiagonalError
    (params : Parameters)
    [FieldModel params.q]
    {strategy : AnswerSymStrat params.next ι}
    (profile : AnswerSuccessorRestrictedFailureProfile params strategy) : Error :=
  avgOver (uniformDistribution (Fq params)) profile.diagonal

/-- Restricted-probabilities statement for an answer-valued successor strategy.

This is a Lean-only statement needed for the simultaneous answer-valued
induction route.  It has the same three averaged conclusions as the restricted
probabilities lemma (`\label{lem:restricted-probabilities}`), with
`xRestrictedAnswerSymStratOfAnswer` as the slice strategy. -/
structure AnswerSuccessorRestrictedProbabilitiesStatement (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error) : Prop where
  /-- There is a slice-wise answer-valued error profile realizing the three
  averaged restricted bounds. -/
  profileExists :
    ∃ profile : AnswerSuccessorRestrictedFailureProfile params strategy,
      averageAnswerSuccessorRestrictedAxisParallelError params profile ≤
          sliceConditioningLoss params * eps ∧
        averageAnswerSuccessorRestrictedSelfConsistencyError params profile ≤ delta ∧
        averageAnswerSuccessorRestrictedDiagonalError params profile ≤
          sliceConditioningLoss params * gamma

/-- The weighted average of the answer-valued successor restricted
axis-parallel slice errors is bounded by the ambient answer-valued
axis-parallel test error. -/
lemma answerSuccessor_weighted_axisParallel_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedAnswerSymStratOfAnswer params strategy x).axisParallelFailureProbability)
      ≤ eps := by
  let carrier := answerSelfImprovementCarrier params.next strategy
  have hcarrier_good :
      carrier.IsGood eps delta carrier.diagonalFailureProbability := by
    refine ⟨?_, ?_, le_rfl⟩
    · simpa [carrier, answerSelfImprovementCarrier,
        SymStrat.axisParallelFailureProbability,
        AnswerSymStrat.axisParallelFailureProbability,
        axisParallelPointAnswerFamily, axisParallelLineAnswerFamily,
        AnswerSymStrat.axisParallelPointAnswerFamily,
        AnswerSymStrat.axisParallelLineAnswerFamily,
        axisParallelPointAnswerFamilyOf, axisParallelLineAnswerFamilyOf] using
        hgood.axisParallelTest
    · simpa [carrier, answerSelfImprovementCarrier,
        SymStrat.selfConsistencyFailureProbability,
        AnswerSymStrat.selfConsistencyFailureProbability] using
        hgood.selfConsistencyTest
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedAnswerSymStratOfAnswer params strategy x).axisParallelFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedAnswerSymStrat params carrier x).axisParallelFailureProbability) := by
            refine avgOver_congr _ _ _ ?_
            intro x
            rfl
    _ ≤ eps :=
        answer_weighted_axisParallel_bound params carrier eps delta
          carrier.diagonalFailureProbability hcarrier_good

/-- Averaging the self-consistency defect over answer-valued successor
restrictions recovers the ambient answer-valued self-consistency defect. -/
lemma answerSuccessor_selfConsistencyRestrictedAverage_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι) :
    avgOver (uniformDistribution (Fq params))
        (fun x =>
          (xRestrictedAnswerSymStratOfAnswer params strategy x).selfConsistencyFailureProbability) =
      strategy.selfConsistencyFailureProbability := by
  let carrier := answerSelfImprovementCarrier params.next strategy
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x =>
          (xRestrictedAnswerSymStratOfAnswer params strategy x).selfConsistencyFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x =>
            (xRestrictedAnswerSymStrat params carrier x).selfConsistencyFailureProbability) := by
            refine avgOver_congr _ _ _ ?_
            intro x
            rfl
    _ = avgOver (uniformDistribution (Fq params))
          (fun x => (xRestrictedStrategy params carrier x).selfConsistencyFailureProbability) := by
            refine avgOver_congr _ _ _ ?_
            intro x
            rw [answerRestricted_selfConsistencyFailureProbability_eq]
    _ = carrier.selfConsistencyFailureProbability :=
        selfConsistencyRestrictedAverage_eq params carrier
    _ = strategy.selfConsistencyFailureProbability := by
        rfl

private lemma answerSuccessorRestrictedDiagonalSampleError_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params)
    (j : Fin params.m)
    (s : RestrictedDiagonalSample params j) :
    qBipartiteConsDefect strategy.state
      (AnswerSymStrat.diagonalPointAnswerFamily
        (xRestrictedAnswerSymStratOfAnswer params strategy x) j s)
      (AnswerSymStrat.diagonalLineAnswerFamily
        (xRestrictedAnswerSymStratOfAnswer params strategy x) j s) =
    qBipartiteConsDefect strategy.state
      (AnswerSymStrat.diagonalPointAnswerFamily strategy (embedCoord params j)
        (appendPoint params s.1 x, s.2))
      (AnswerSymStrat.diagonalLineAnswerFamily strategy (embedCoord params j)
        (appendPoint params s.1 x, s.2)) := by
  have hdir :
      appendPoint params (extendRestrictedDirection j s.2) zeroCoord =
        extendRestrictedDirection (params := params.next) (embedCoord params j) s.2 := by
    funext k
    by_cases hkm : k.1 < params.m
    · by_cases hk : k.1 ≤ j.1
      · simp [appendPoint, extendRestrictedDirection, embedCoord, hkm, hk]
      · simp [appendPoint, extendRestrictedDirection, embedCoord, hkm, hk]
        rfl
    · have hnotle : ¬ k.1 ≤ j.1 := by
          intro hk
          exact hkm (lt_of_le_of_lt hk j.2)
      simp [appendPoint, extendRestrictedDirection, embedCoord, hkm, hnotle]
      rfl
  have hline :
      DiagonalLine.appendAtHeight params
          { base := s.1, direction := extendRestrictedDirection j s.2 } x =
        ({ base := appendPoint params s.1 x,
           direction :=
             extendRestrictedDirection (params := params.next) (embedCoord params j) s.2 } :
          DiagonalLine params.next) := by
    simp [DiagonalLine.appendAtHeight, hdir]
  simp [AnswerSymStrat.diagonalPointAnswerFamily,
    AnswerSymStrat.diagonalLineAnswerFamily, xRestrictedAnswerSymStratOfAnswer]
  simp [diagonalPointAnswerFamilyOf, diagonalLineAnswerFamilyOf, hline]
  rfl

private noncomputable def answerSuccessorDiagonalSliceIndexError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params)
    (j : Fin params.m) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (RestrictedDiagonalSample params j))
    (AnswerSymStrat.diagonalPointAnswerFamily
      (xRestrictedAnswerSymStratOfAnswer params strategy x) j)
    (AnswerSymStrat.diagonalLineAnswerFamily
      (xRestrictedAnswerSymStratOfAnswer params strategy x) j)

private noncomputable def answerSuccessorDiagonalIndexError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (j : Fin params.next.m) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (RestrictedDiagonalSample params.next j))
    (AnswerSymStrat.diagonalPointAnswerFamily strategy j)
    (AnswerSymStrat.diagonalLineAnswerFamily strategy j)

private lemma answerSuccessorDiagonalSliceIndexErrorAverage_eq_diagonalIndexError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (j : Fin params.m) :
    avgOver (uniformDistribution (Fq params))
      (fun x => answerSuccessorDiagonalSliceIndexError params strategy x j) =
      answerSuccessorDiagonalIndexError params strategy (embedCoord params j) := by
  let g : RestrictedDiagonalSample params.next (embedCoord params j) → Error := fun s =>
    qBipartiteConsDefect strategy.state
      (AnswerSymStrat.diagonalPointAnswerFamily strategy (embedCoord params j) s)
      (AnswerSymStrat.diagonalLineAnswerFamily strategy (embedCoord params j) s)
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => answerSuccessorDiagonalSliceIndexError params strategy x j)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (RestrictedDiagonalSample params j))
            (fun s => g (appendPoint params s.1 x, s.2))) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              unfold answerSuccessorDiagonalSliceIndexError bipartiteConsError
              refine avgOver_congr _ _ _ ?_
              intro s
              simpa [g] using
                answerSuccessorRestrictedDiagonalSampleError_eq params strategy x j s
    _ = avgOver (uniformDistribution (Fq params × RestrictedDiagonalSample params j))
          (fun xs => g (appendPoint params xs.2.1 xs.1, xs.2.2)) := by
            simpa using
              (avgOver_uniform_prod (α := Fq params)
                (β := RestrictedDiagonalSample params j)
                (f := fun x s => g (appendPoint params s.1 x, s.2))).symm
    _ = avgOver
          (uniformDistribution (RestrictedDiagonalSample params.next (embedCoord params j)))
          g := by
            exact avgOver_uniform_restrictedDiagonalSample_append params j g
    _ = answerSuccessorDiagonalIndexError params strategy (embedCoord params j) := by
            rfl

private lemma answerSuccessorAverageRestrictedDiagonalFailure_eq_embeddedDiagonalIndices
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι) :
    avgOver (uniformDistribution (Fq params))
      (fun x => (xRestrictedAnswerSymStratOfAnswer params strategy x).diagonalFailureProbability) =
    avgOver (uniformDistribution (Fin params.m))
      (fun j => answerSuccessorDiagonalIndexError params strategy (embedCoord params j)) := by
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => (xRestrictedAnswerSymStratOfAnswer params strategy x).diagonalFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Fin params.m))
            (fun j => answerSuccessorDiagonalSliceIndexError params strategy x j)) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              unfold AnswerSymStrat.diagonalFailureProbability
                answerSuccessorDiagonalSliceIndexError
              calc
                (1 / (params.m : Error)) *
                    ∑ j : Fin params.m,
                      bipartiteConsError strategy.state
                        (uniformDistribution (RestrictedDiagonalSample params j))
                        (AnswerSymStrat.diagonalPointAnswerFamily
                          (xRestrictedAnswerSymStratOfAnswer params strategy x) j)
                        (AnswerSymStrat.diagonalLineAnswerFamily
                          (xRestrictedAnswerSymStratOfAnswer params strategy x) j)
                  = ∑ j : Fin params.m,
                      (1 / (params.m : Error)) *
                        bipartiteConsError strategy.state
                          (uniformDistribution (RestrictedDiagonalSample params j))
                          (AnswerSymStrat.diagonalPointAnswerFamily
                            (xRestrictedAnswerSymStratOfAnswer params strategy x) j)
                          (AnswerSymStrat.diagonalLineAnswerFamily
                            (xRestrictedAnswerSymStratOfAnswer params strategy x) j) := by
                              rw [Finset.mul_sum]
                _ = avgOver (uniformDistribution (Fin params.m))
                      (fun j => answerSuccessorDiagonalSliceIndexError params strategy x j) := by
                              simp [avgOver, uniformDistribution, Fintype.card_fin,
                                answerSuccessorDiagonalSliceIndexError]
    _ = avgOver (uniformDistribution (Fin params.m))
          (fun j => avgOver (uniformDistribution (Fq params))
            (fun x => answerSuccessorDiagonalSliceIndexError params strategy x j)) := by
            exact avgOver_uniform_comm
              (fun x j => answerSuccessorDiagonalSliceIndexError params strategy x j)
    _ = avgOver (uniformDistribution (Fin params.m))
          (fun j => answerSuccessorDiagonalIndexError params strategy (embedCoord params j)) := by
            refine avgOver_congr _ _ _ ?_
            intro j
            exact answerSuccessorDiagonalSliceIndexErrorAverage_eq_diagonalIndexError
              params strategy j

/-- The weighted average of the answer-valued successor restricted diagonal
slice errors is bounded by the ambient answer-valued diagonal-line test error. -/
lemma answerSuccessor_weighted_diagonal_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedAnswerSymStratOfAnswer params strategy x).diagonalFailureProbability)
      ≤ gamma := by
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedAnswerSymStratOfAnswer params strategy x).diagonalFailureProbability)
      = sliceTransverseDirectionWeight params *
          avgOver (uniformDistribution (Fq params))
            (fun x =>
              AnswerSymStrat.diagonalFailureProbability
                (xRestrictedAnswerSymStratOfAnswer params strategy x)) := by
              rw [avgOver_const_mul]
    _ = sliceTransverseDirectionWeight params *
          avgOver (uniformDistribution (Fin params.m))
            (fun j => answerSuccessorDiagonalIndexError params strategy (embedCoord params j)) := by
              rw [answerSuccessorAverageRestrictedDiagonalFailure_eq_embeddedDiagonalIndices
                params strategy]
    _ ≤ avgOver (uniformDistribution (Fin params.next.m))
          (answerSuccessorDiagonalIndexError params strategy) :=
        weighted_embedded_average_le_full_average params
          (f := answerSuccessorDiagonalIndexError params strategy)
          (hf := by
            intro j
            unfold answerSuccessorDiagonalIndexError
            exact bipartiteConsError_nonneg strategy.state
              (uniformDistribution (RestrictedDiagonalSample params.next j))
              (AnswerSymStrat.diagonalPointAnswerFamily strategy j)
              (AnswerSymStrat.diagonalLineAnswerFamily strategy j))
    _ = strategy.diagonalFailureProbability := by
        unfold answerSuccessorDiagonalIndexError AnswerSymStrat.diagonalFailureProbability
        calc
          avgOver (uniformDistribution (Fin params.next.m))
              (fun j =>
                bipartiteConsError strategy.state
                  (uniformDistribution (RestrictedDiagonalSample params.next j))
                  (AnswerSymStrat.diagonalPointAnswerFamily strategy j)
                  (AnswerSymStrat.diagonalLineAnswerFamily strategy j))
            = ∑ j : Fin params.next.m,
                (1 / (params.next.m : Error)) *
                  bipartiteConsError strategy.state
                    (uniformDistribution (RestrictedDiagonalSample params.next j))
                    (AnswerSymStrat.diagonalPointAnswerFamily strategy j)
                    (AnswerSymStrat.diagonalLineAnswerFamily strategy j) := by
                      simp [avgOver, uniformDistribution, Fintype.card_fin]
          _ = (1 / (params.next.m : Error)) *
                ∑ j : Fin params.next.m,
                  bipartiteConsError strategy.state
                    (uniformDistribution (RestrictedDiagonalSample params.next j))
                    (AnswerSymStrat.diagonalPointAnswerFamily strategy j)
                    (AnswerSymStrat.diagonalLineAnswerFamily strategy j) := by
                      symm
                      rw [Finset.mul_sum]
          _ = strategy.diagonalFailureProbability := by
                rfl
    _ ≤ gamma := hgood.diagonalLineTest

/-- Assemble the weighted answer-valued successor restricted-probability bounds
into the averaged statement. -/
lemma AnswerSuccessorRestrictedProbabilitiesStatement.ofWeightedBounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (haxisWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedAnswerSymStratOfAnswer params strategy x).axisParallelFailureProbability)
        ≤ eps)
    (hdiagonalWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedAnswerSymStratOfAnswer params strategy x).diagonalFailureProbability)
        ≤ gamma) :
    AnswerSuccessorRestrictedProbabilitiesStatement params strategy eps delta gamma := by
  let profile : AnswerSuccessorRestrictedFailureProfile params strategy :=
    { axisParallel := fun x =>
        (xRestrictedAnswerSymStratOfAnswer params strategy x).axisParallelFailureProbability
      selfConsistency := fun x =>
        (xRestrictedAnswerSymStratOfAnswer params strategy x).selfConsistencyFailureProbability
      diagonal := fun x =>
        (xRestrictedAnswerSymStratOfAnswer params strategy x).diagonalFailureProbability
      restrictedGood := fun _ => ⟨le_rfl, le_rfl, le_rfl⟩ }
  have haxis_weighted_avg :
      sliceTransverseDirectionWeight params *
          averageAnswerSuccessorRestrictedAxisParallelError params profile ≤ eps := by
    simpa [profile, averageAnswerSuccessorRestrictedAxisParallelError, avgOver_const_mul] using
      haxisWeightedBound
  have hdiag_weighted_avg :
      sliceTransverseDirectionWeight params *
          averageAnswerSuccessorRestrictedDiagonalError params profile ≤ gamma := by
    simpa [profile, averageAnswerSuccessorRestrictedDiagonalError, avgOver_const_mul] using
      hdiagonalWeightedBound
  refine ⟨profile, ?_⟩
  refine ⟨weighted_bound_to_average params haxis_weighted_avg, ?_, ?_⟩
  · calc
      averageAnswerSuccessorRestrictedSelfConsistencyError params profile
        = avgOver (uniformDistribution (Fq params))
            (fun x =>
              AnswerSymStrat.selfConsistencyFailureProbability
                (xRestrictedAnswerSymStratOfAnswer params strategy x)) := by
            rfl
      _ = strategy.selfConsistencyFailureProbability := by
            exact answerSuccessor_selfConsistencyRestrictedAverage_eq params strategy
      _ ≤ delta := hgood.selfConsistencyTest
  · exact weighted_bound_to_average params hdiag_weighted_avg

/-- Answer-valued restricted-probabilities theorem for an answer-valued
successor strategy.

This is the restricted-probability input needed by a simultaneous
answer-valued proof of the main induction theorem.  It is a construction from
the answer-valued successor strategy's own goodness hypotheses, not an
additional theorem assumption. -/
lemma answerSuccessorRestrictedProbabilities
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    AnswerSuccessorRestrictedProbabilitiesStatement params strategy eps delta gamma := by
  exact AnswerSuccessorRestrictedProbabilitiesStatement.ofWeightedBounds
    params strategy eps delta gamma hgood
    (answerSuccessor_weighted_axisParallel_bound params strategy eps delta gamma hgood)
    (answerSuccessor_weighted_diagonal_bound params strategy eps delta gamma hgood)

end MIPStarRE.LDT.MainInductionStep
