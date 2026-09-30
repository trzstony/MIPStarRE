import MIPStarRE.LDT.MainInductionStep.Theorems.PastingAssembly.Basic

/-!
# Section 6 — Pasting Assembly: Answer-Valued Fields

This module assembles the answer-valued averaged family fields and the
commutativity input used by the pasting theorem.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- Answer-valued Section 11 commutativity input needed by the positive-degree
pasting branch.

This is a Lean-only construction target, not a source theorem and not a
hypothesis of `thm:main-induction`.  It is the precise replacement for the invalid route
through the ordinary carrier's dummy diagonal measurement: the conclusion is
the ordinary `ComMainConclusion` for the point-equivalent carrier, but the
intended proof must use the answer-valued diagonal verifier relation of
`strategy`.

The proof first establishes the Section 10 point-commutativity estimate from
the answer-valued diagonal-line test, transfers that estimate to the
point-equivalent carrier, and then invokes the Section 11 scalar chain in its
form that assumes point commutativity rather than an ordinary diagonal
`IsGood` field. -/
theorem answerComMainForCarrier_ofAnswerGood
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_nonneg : 0 ≤ gamma)
    (family : IdxPolyFamily params ι)
    (hcons :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxPolyFamily.evaluatedAtNextPoint family)
        zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound :
      IdxPolyFamily.SliceBoundednessInput
        (answerSelfImprovementCarrier params.next strategy)
        family zeta) :
    Commutativity.ComMainConclusion params
      (answerSelfImprovementCarrier params.next strategy) family gamma zeta := by
  let carrier : SymStrat params.next ι := answerSelfImprovementCarrier params.next strategy
  have hcommAnswer :
      SDDOpRel strategy.state
        (uniformDistribution (MIPStarRE.LDT.GlobalVariance.PointPairQuestion params.next))
        (CommutativityPoints.answerPointMeasurementProductLeft params.next strategy)
        (CommutativityPoints.answerPointMeasurementProductRight params.next strategy)
        (CommutativityPoints.commutativityPointsError params.next gamma) :=
    CommutativityPoints.answerCommutativityPoints
      (params := params.next) strategy eps delta gamma hgood
  have hcommCarrier :
      SDDOpRel carrier.state
        (uniformDistribution (MIPStarRE.LDT.GlobalVariance.PointPairQuestion params.next))
        (CommutativityPoints.pointMeasurementProductLeft params.next carrier)
        (CommutativityPoints.pointMeasurementProductRight params.next carrier)
        (CommutativityPoints.commutativityPointsError params.next gamma) := by
    change SDDOpRel strategy.state
      (uniformDistribution (MIPStarRE.LDT.GlobalVariance.PointPairQuestion params.next))
      (CommutativityPoints.answerPointMeasurementProductLeft params.next strategy)
      (CommutativityPoints.answerPointMeasurementProductRight params.next strategy)
      (CommutativityPoints.commutativityPointsError params.next gamma)
    exact hcommAnswer
  have hconsCarrier : family.ConsistentWithPoints carrier zeta := by
    exact ⟨by simpa [carrier, answerSelfImprovementCarrier] using hcons⟩
  exact
    Commutativity.comMain_of_commutativityPoints
      params carrier gamma zeta carrier.isNormalized hcommCarrier hgamma_nonneg
      family hconsCarrier hself hbound

end MIPStarRE.LDT.MainInductionStep
