import MIPStarRE.LDT.Pasting.Simplified.DistinctSuccessConsistency
import MIPStarRE.LDT.Pasting.ComparisonLemmas.LineInterpolation.HBError

/-!
# Bad mass for distinct-success interpolation

The new interpolant's line-inconsistency mass is bounded by the existing
all-successful-position mismatch mass. This reduction uses the selected
slice interpolation property and requires no global distinctness of the
question tuple.

## References

- `blueprint/src/low_degree_simplified.tex`, `lem:pasting-consistency`.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Scalar mass of eligible completed words whose selected interpolant
disagrees with Bob's vertical-line answer. -/
noncomputable def distinctSuccessBadMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) (xs : PointTuple params k) : Error :=
  ∑ f : AxisLinePolynomial params.next,
    ev strategy.state
      (opTensor
        (∑ gs : GHatTupleOutcome params k,
          if HasDistinctSuccessSupport params xs gs ∧
              distinctSuccessVerticalLine params u xs gs ≠ f then
            (gHatSandwichFamily params family k xs).outcome gs else 0)
        ((verticalLineMeasurementFamily params strategy u).outcome f))

/-- Restricting the pasted answer to a vertical line and then testing one
line outcome is the same as testing the selected interpolant directly. -/
theorem distinctSuccess_verticalLine_singleOutcome_postprocess
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) (xs : PointTuple params k)
    (f : AxisLinePolynomial params.next) :
    postprocess
      (hRestrictionToVerticalLine params
        (distinctSuccessSandwichFamily params family k xs) u)
      (fun h => decide (h = f)) =
    postprocess
      (restrictSubMeas (gHatSandwichFamily params family k xs)
        (HasDistinctSuccessSupport params xs))
      (fun gs => decide (distinctSuccessVerticalLine params u xs gs = f)) := by
  rw [distinctSuccessSandwichFamily, hRestrictionToVerticalLine]
  rw [postprocess_postprocess, postprocess_postprocess]
  congr 1

/-- The one-question bipartite consistency defect of the new pasted slice
family is exactly its bad mass against the vertical-line measurement. -/
theorem distinctSuccess_verticalLine_defect_eq_badMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) (xs : PointTuple params k) :
    qBipartiteConsDefect strategy.state
      (hRestrictionToVerticalLine params
        (distinctSuccessSandwichFamily params family k xs) u)
      (verticalLineMeasurementFamily params strategy u) =
        distinctSuccessBadMass params strategy family u xs := by
  classical
  let ℓ : AxisParallelLine params.next :=
    { base := appendPoint params u zeroCoord
      direction := lastCoord params }
  let Bm : Measurement (AxisLinePolynomial params.next) ι :=
    (strategy.axisParallelMeasurement ℓ).toMeasurement
  have hB : Bm.toSubMeas = verticalLineMeasurementFamily params strategy u := by
    simp [Bm, ℓ, verticalLineMeasurementFamily]
  rw [← hB, qBipartiteConsDefect_eq_sum_singleOutcome (B := Bm)]
  unfold distinctSuccessBadMass
  apply Finset.sum_congr rfl
  intro f _
  calc
    qBipartiteConsDefect strategy.state
        (postprocess
          (hRestrictionToVerticalLine params
            (distinctSuccessSandwichFamily params family k xs) u)
          (fun h => decide (h = f)))
        (singleOutcomeRightSubMeas Bm.toSubMeas f) =
      ev strategy.state
        (opTensor
          ((postprocess
            (hRestrictionToVerticalLine params
              (distinctSuccessSandwichFamily params family k xs) u)
            (fun h => decide (h = f))).outcome false)
          (Bm.outcome f)) := by
            rw [qBipartiteConsDefect_postprocess_eq_singleOutcome]
    _ = ev strategy.state
        (opTensor
          (∑ gs : GHatTupleOutcome params k,
            if HasDistinctSuccessSupport params xs gs ∧
                distinctSuccessVerticalLine params u xs gs ≠ f then
              (gHatSandwichFamily params family k xs).outcome gs else 0)
          (Bm.outcome f)) := by
            rw [distinctSuccess_verticalLine_singleOutcome_postprocess,
              postprocess_restrictSubMeas_outcome]
            simp [decide_eq_false_iff_not]
    _ = ev strategy.state
        (opTensor
          (∑ gs : GHatTupleOutcome params k,
            if HasDistinctSuccessSupport params xs gs ∧
                distinctSuccessVerticalLine params u xs gs ≠ f then
              (gHatSandwichFamily params family k xs).outcome gs else 0)
          ((verticalLineMeasurementFamily params strategy u).outcome f)) := by
            simp [hB]

/-- The defect of the averaged pasted submeasurement is controlled by the
average bad mass of its questionwise distinct-success construction. -/
theorem distinctSuccessPasted_verticalLine_defect_le_badMass_average
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ)
    (u : Point params) :
    qBipartiteConsDefect strategy.state
        (hRestrictionToVerticalLine params
          (distinctSuccessPastedSubMeas params family k) u)
        (verticalLineMeasurementFamily params strategy u) ≤
      avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        distinctSuccessBadMass params strategy family u xs) := by
  rw [distinctSuccessPastedSubMeas,
    hRestrictionToVerticalLine_averageIdxSubMeas]
  calc
    qBipartiteConsDefect strategy.state
        (averageIdxSubMeas (uniformDistribution (PointTuple params k))
          (fun xs => hRestrictionToVerticalLine params
            (distinctSuccessSandwichFamily params family k xs) u)
          (uniformDistribution_weight_sum_le_one (PointTuple params k)))
        (verticalLineMeasurementFamily params strategy u) ≤
      avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        qBipartiteConsDefect strategy.state
          (hRestrictionToVerticalLine params
            (distinctSuccessSandwichFamily params family k xs) u)
          (verticalLineMeasurementFamily params strategy u)) := by
            exact qBipartiteConsDefect_averageIdxSubMeas_left_le
              strategy.state (uniformDistribution (PointTuple params k))
              (fun xs => hRestrictionToVerticalLine params
                (distinctSuccessSandwichFamily params family k xs) u)
              (verticalLineMeasurementFamily params strategy u)
              (uniformDistribution_weight_sum_le_one (PointTuple params k))
    _ = avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
          distinctSuccessBadMass params strategy family u xs) := by
            exact avgOver_congr _ _ _ fun xs =>
              distinctSuccess_verticalLine_defect_eq_badMass
                params strategy family u xs

/-- Every new bad outcome is counted by the established mismatch mass
for the cardinality-only eligible sandwich family. -/
theorem distinctSuccessBadMass_le_hBConsistencyBadMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) (xs : PointTuple params k) :
    distinctSuccessBadMass params strategy family u xs ≤
      hBConsistencyBadMass params strategy family u xs := by
  classical
  unfold distinctSuccessBadMass hBConsistencyBadMass
  apply Finset.sum_le_sum
  intro f _
  apply ev_mono strategy.state _ _
  apply opTensor_mono_left _
    ((verticalLineMeasurementFamily params strategy u).outcome_pos f)
  apply Finset.sum_le_sum
  intro gs _
  by_cases hbad : HasDistinctSuccessSupport params xs gs ∧
      distinctSuccessVerticalLine params u xs gs ≠ f
  · obtain ⟨h, hne⟩ := hbad
    obtain ⟨i, _, hiSome, hm⟩ :=
      distinctSuccessVerticalLine_ne_gives_selected_mismatch
        params u xs gs h f hne
    have hright :
        ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
          ((gs i).get hiSome) u ≠ f (xs i) := ⟨i, hiSome, hm⟩
    have hold : InterpolationEligible params gs :=
      hasDistinctSuccessSupport_interpolationEligible params xs gs h
    simp [h, hne, hright, interpolationEligibleSandwichFamily,
      restrictSubMeas, hold]
  · by_cases hright :
        ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
          ((gs i).get hiSome) u ≠ f (xs i)
    · simp only [if_neg hbad, if_pos hright]
      exact (interpolationEligibleSandwichFamily params family k xs).outcome_pos gs
    · simp [hbad, hright]

/-- The new bad mass inherits the existing sum of one-point consistency
defects. -/
theorem distinctSuccessBadMass_le_linePointDefectSum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) (xs : PointTuple params k) :
    distinctSuccessBadMass params strategy family u xs ≤
      ∑ i : Fin k,
        qBipartiteConsDefect strategy.state
          ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) (u, xs))
          ((ldSandwichLineOnePointRightFamily params strategy family k i.1) (u, xs)) := by
  exact (distinctSuccessBadMass_le_hBConsistencyBadMass
    params strategy family u xs).trans
    (hBConsistencyBadMass_le_linePointDefectSum
      params strategy family u xs)

end MIPStarRE.LDT.Pasting
