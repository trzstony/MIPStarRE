import MIPStarRE.LDT.Commutativity.Main.EvaluatedQuestions
import MIPStarRE.LDT.Commutativity.ScalarApproximation.ProcessedG

/-!
# Section 11 commutativity: final results

Top-level `thm:com-main` statement, lifting evaluated commutation back to
full-slice commutation via the two-step Schwartz–Zippel marginalization.

The two-step lift uses a hybrid scalar/tensor architecture (Option 3):
the public conclusion is an `SDDOpRel` on operator families, composed from
scalar transport lemmas whose proofs internally use tensor-form intermediates
for the PSD Schwartz–Zippel argument.
See `docs/decisions/713-scalar-tensor-decision.md`.

## References

- `references/ldt-paper/commutativity-points.tex`
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Paper origin: `references/ldt-paper/commutativity-G.tex`
(`\label{thm:com-main}`).

The paper theorem is formulated directly for the family `family.meas`; any
explicit auxiliary family used by the scalar approximation proof is internal to
the proof. -/
theorem comMain_of_commutativityPoints
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (gamma zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hcomm :
      SDDOpRel strategy.state
        (uniformDistribution (MIPStarRE.LDT.GlobalVariance.PointPairQuestion params.next))
        (pointMeasurementProductLeft params.next strategy)
        (pointMeasurementProductRight params.next strategy)
        (commutativityPointsError params.next gamma))
    (hgamma_nonneg : 0 ≤ gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    ComMainConclusion params strategy family gamma zeta := by
  let hEval :=
    commDataProcessedG_of_commutativityPoints
      params strategy gamma zeta hnorm hcomm hgamma_nonneg family hcons hself hbound
  have hSpecialized :
      SDDOpRel strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedFromFullSliceProductLeft params strategy family)
        (evaluatedFromFullSliceProductRight params strategy family)
        (commDataProcessedGError params gamma zeta) := by
    constructor
    rw [evaluationSpecialization_sddErrorOp_eq]
    exact hEval.squaredDistanceBound
  have hzeta_nonneg : 0 ≤ zeta :=
    le_trans (sddError_nonneg _ _ _ _)
      hself.sliceSelfConsistency.squaredDistanceBound
  exact
    sddOpRel_of_pullback_fullSliceQuestion params strategy.state
      (fullSliceProductLeft params strategy family)
      (fullSliceProductRight params strategy family)
      (comMainError params gamma zeta)
      (fullSliceCommutation_of_evaluated_on_evaluated_questions
        params strategy family gamma zeta
        hnorm hgamma_nonneg hzeta_nonneg hself hSpecialized)

end MIPStarRE.LDT.Commutativity
