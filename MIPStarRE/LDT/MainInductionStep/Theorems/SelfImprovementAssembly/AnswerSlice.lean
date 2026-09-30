import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import MIPStarRE.LDT.Pasting.Bernoulli.ScalarBounds
import MIPStarRE.LDT.Pasting.ComparisonLemmas.LineInterpolation.HBError
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.SelfImprovementTop.Core

/-!
# Section 6 — Answer-Valued Self-Improvement Slice Transport

This file contains the answer-valued analogues of the Section 6 slice-transport
constructors.  The ordinary construction, including `selfImprovementInInductionSection`,
lives in `SelfImprovementAssembly.Core` and is imported here so that the
answer-valued construction can reuse the same Section 9 self-improvement
theorem.

## References

- `blueprint/src/chapter/ch10_induction.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- A covariant diagonal measurement with a fixed zero polynomial outcome.

This measurement is used only as an inert diagonal component when applying the
axis-parallel/self-consistency form of self-improvement to an answer-valued
slice.  The Section 9 conclusion obtained in this way is independent of the
diagonal-line failure probability. -/
noncomputable def dummyDiagonalCovariantMeasurement
    (params : Parameters)
    [FieldModel params.q]
    (ι : Type uι) [Fintype ι] [DecidableEq ι] :
    DiagonalCovariantMeasurement params ι where
  toIdxProjMeas := fun _ =>
    ProjMeas.trivialDistinguishedOutcome (default : DiagonalLinePolynomial params)
  transportInvariant := fun _ t =>
    ((ProjMeas.transport_trivialDistinguishedOutcome
      (DiagonalLinePolynomial.reparamAtEquiv (params := params) t)
      (default : DiagonalLinePolynomial params)).trans
        (congrArg (ProjMeas.trivialDistinguishedOutcome (ι := ι))
          (DiagonalLinePolynomial.reparamAt_default t))).symm

/-- Forget the answer-valued diagonal alphabet of a restricted slice, replacing
it by an inert ordinary diagonal measurement.

The point, axis-parallel, state, and normalization data are unchanged.  This is
therefore sufficient for the self-improvement theorem variant whose hypotheses
are exactly the axis-parallel and point self-consistency bounds. -/
noncomputable def answerSelfImprovementCarrier
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    SymStrat params ι where
  state := strategy.state
  permInvState := strategy.permInvState
  densityFixed := strategy.densityFixed
  isNormalized := strategy.isNormalized
  pointMeasurement := strategy.pointMeasurement
  axisParallelMeasurement := strategy.axisParallelMeasurement
  diagonalMeasurement := dummyDiagonalCovariantMeasurement params ι

/-- Restrict an answer-valued diagonal-line measurement to the slice at height
`x`.

This is the answer-valued analogue of `restrictDiagonalAnswerMeasurement`.
Because the diagonal answer alphabet is the full function space on the line,
restriction is the total map
`DiagonalLineAnswer.restrictAtHeight`; no low-degree support theorem is needed
to define this slice. -/
noncomputable def restrictAnswerDiagonalAnswerMeasurement
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params) :
    IdxProjMeas (DiagonalLine params) (DiagonalLineAnswer params) ι :=
  fun ℓ =>
    ProjMeas.postprocess
      (strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x))
      (fun f : DiagonalLineAnswer params.next =>
        DiagonalLineAnswer.restrictAtHeight params f x)

/-- Transport covariance for the answer-valued restricted diagonal-line
measurement. -/
private theorem restrictAnswerDiagonalAnswerMeasurement_transportInvariant
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params) :
    DiagonalAnswerMeasurementTransportInvariant params
      (restrictAnswerDiagonalAnswerMeasurement params strategy x) := by
  intro ℓ t
  apply ProjMeas.ext
  intro a
  have htransport :=
    MIPStarRE.LDT.DiagonalAnswerCovariantMeasurement.transportInvariant
      strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x) t
  let A := (strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x)).toSubMeas
  let eNext := DiagonalLineAnswer.reparamAtEquiv (params := params.next) t
  let eSlice := DiagonalLineAnswer.reparamAtEquiv (params := params) t
  let f : DiagonalLineAnswer params.next → DiagonalLineAnswer params :=
    fun g => DiagonalLineAnswer.restrictAtHeight params g x
  have hcomm : ∀ g, f (eNext g) = eSlice (f g) := by
    intro g
    funext s
    rfl
  have hpost : postprocess (SubMeas.transport eNext A) f =
      SubMeas.transport eSlice (postprocess A f) :=
    SubMeas.postprocess_transport_equiv eNext eSlice A f f hcomm
  exact congrArg (fun M : SubMeas (DiagonalLineAnswer params) ι => M.outcome a) <| by
    simpa [restrictAnswerDiagonalAnswerMeasurement, DiagonalLine.transportMeasurement,
      ProjMeas.transport, Measurement.transport, A, eNext, eSlice, f,
      DiagonalLine.appendAtHeight_rebaseAt, htransport] using hpost

/-- Evaluating the answer-valued restricted diagonal measurement at the base point
recovers the ambient answer-valued diagonal readout. -/
@[simp] theorem restrictAnswerDiagonalAnswerMeasurement_postprocess_zero
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params)
    (ℓ : DiagonalLine params) :
    postprocess ((restrictAnswerDiagonalAnswerMeasurement params strategy x ℓ).toSubMeas)
        (fun f : DiagonalLineAnswer params => f zeroCoord) =
      postprocess
        ((strategy.diagonalMeasurement
          (DiagonalLine.appendAtHeight params ℓ x)).toSubMeas)
        (fun f : DiagonalLineAnswer params.next => f zeroCoord) := by
  simp [restrictAnswerDiagonalAnswerMeasurement, ProjMeas.postprocess_toSubMeas,
    SubMeas.postprocess_comp, DiagonalLineAnswer.restrictAtHeight]
  rfl

/-- The `x`-restricted strategy of an answer-valued successor strategy.

Paper origin: `references/ldt-paper/inductive_step.tex:436-455`, in the
answer-valued strategy interface used for the recursive slice call.

This is the recursive restriction map needed for a simultaneous answer-valued
form of the main induction theorem.  It preserves the state, point
measurement, axis-parallel measurement, and full answer-valued diagonal
measurement on the slice. -/
noncomputable def xRestrictedAnswerSymStratOfAnswer
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params) : AnswerSymStrat params ι where
  state := strategy.state
  permInvState := strategy.permInvState
  densityFixed := strategy.densityFixed
  isNormalized := strategy.isNormalized
  pointMeasurement := fun u => strategy.pointMeasurement (appendPoint params u x)
  axisParallelMeasurement :=
    (xRestrictedAnswerSymStrat params
      (answerSelfImprovementCarrier params.next strategy) x).axisParallelMeasurement
  diagonalMeasurement :=
    { toIdxProjMeas := restrictAnswerDiagonalAnswerMeasurement params strategy x
      transportInvariant :=
        restrictAnswerDiagonalAnswerMeasurement_transportInvariant params strategy x }

/-- Answer-valued slice restriction does not change the bipartite state. -/
@[simp] theorem xRestrictedAnswerSymStratOfAnswer_state
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params) :
    (xRestrictedAnswerSymStratOfAnswer params strategy x).state = strategy.state :=
  rfl

/-- Answer-valued slice restriction reindexes point questions by appending the
slice height. -/
@[simp] theorem xRestrictedAnswerSymStratOfAnswer_pointMeasurement_apply
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params)
    (u : Point params) :
    (xRestrictedAnswerSymStratOfAnswer params strategy x).pointMeasurement u =
      strategy.pointMeasurement (appendPoint params u x) :=
  rfl

/-- Answer-valued slice restriction reuses the parent normalization witness. -/
@[simp] theorem xRestrictedAnswerSymStratOfAnswer_isNormalized
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params) :
    (xRestrictedAnswerSymStratOfAnswer params strategy x).isNormalized =
      strategy.isNormalized :=
  rfl

/-- The diagonal measurement of an answer-valued slice is the full answer-valued
restriction of the ambient diagonal measurement. -/
@[simp] theorem xRestrictedAnswerSymStratOfAnswer_diagonalMeasurement_apply
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params)
    (ℓ : DiagonalLine params) :
    (xRestrictedAnswerSymStratOfAnswer params strategy x).diagonalMeasurement ℓ =
      restrictAnswerDiagonalAnswerMeasurement params strategy x ℓ :=
  rfl

end MIPStarRE.LDT.MainInductionStep
