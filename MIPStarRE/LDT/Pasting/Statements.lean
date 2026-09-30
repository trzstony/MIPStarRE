import MIPStarRE.LDT.Commutativity.Scaffold.Core
import MIPStarRE.LDT.MainInductionStep.Defs
import MIPStarRE.LDT.Pasting.Sandwich.PastedFamilies

/-!
# Section 12 — Statements

This file records the Section 12 pasting conclusions as reusable proposition-valued
structures. It gives the displayed error formulas and the statement structures for the
switcheroo, completed-family, half-sandwich, recurrence, Chernoff, and final pasting steps.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Displayed error term for `lem:commutativity-switcheroo`. -/
noncomputable def commutativitySwitcherooError
    (zeta omega chi : Error) : Error :=
  6 * Real.rpow zeta (1 / (2 : Error)) +
    6 * Real.rpow omega (1 / (2 : Error)) +
    4 * Real.rpow chi (1 / (2 : Error))

/-- Displayed error term for `cor:commuting-with-G-complete`. -/
noncomputable def commutingWithGCompleteError (params : Parameters)
    (gamma zeta : Error) : Error :=
  36 * (params.m : Error) *
    (Real.rpow gamma (1 / (16 : Error)) +
      Real.rpow zeta (1 / (16 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)))

/-- Displayed error term for `cor:commuting-with-G-incomplete`. -/
noncomputable def commutingWithGIncompleteError (params : Parameters)
    (gamma zeta : Error) : Error :=
  commutingWithGCompleteError params gamma zeta

/-- Displayed error term for the pairwise complete-part commutation bound used in
`cor:G-hat-facts`.

This is exactly the upstream `thm:com-main` error term. The proof of
`cor:G-hat-facts` only weakens the exponent to `1/16` after adding the three
incomplete-part commutation contributions. -/
noncomputable def pairwiseCompletePartCommutationError (params : Parameters)
    (gamma zeta : Error) : Error :=
  Commutativity.comMainError params gamma zeta

/-- Displayed self-consistency error for `\widehat G`. -/
def gHatSelfConsistencyError (zeta : Error) : Error :=
  2 * zeta

/-- Displayed commutation error for `\widehat G`. -/
noncomputable def gHatCommutationError (params : Parameters)
    (gamma zeta : Error) : Error :=
  138 * (params.m : Error) *
    (Real.rpow gamma (1 / (16 : Error)) +
      Real.rpow zeta (1 / (16 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)))

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:514-536`
(`\label{lem:g-complete-self-consistency}`); the `\widehat G` rewrite at
`eq:gselfconall` (`references/ldt-paper/ld-pasting.tex:821`) is the family of
self-consistency bounds compared against here.

Lean statement for `lem:g-complete-self-consistency`.
`ψbi` is the bipartite state on `d * d` (passed as `strategy.state`
by callers). -/
structure GCompleteSelfConsistencyStatement (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (zeta : Error) : Prop where
  /--
  Stores self-consistency of the full slice family `family.meas` because the
  `cor:G-hat-facts` decomposition expands `\widehat G` self-consistency into the
  original slice-family term plus the incomplete part, not the postprocessed
  complete-part family.
  -/
  completePartSelfConsistency :
    SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas))
      (IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas))
      zeta

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:537-558`
(`\label{cor:g-bot-self-consistency}`); incomplete-part complement of
`\label{lem:g-complete-self-consistency}` and the
`eq:gselfconall` self-consistency family at line 821.

Lean statement for `cor:g-bot-self-consistency`. -/
structure GBotSelfConsistencyStatement (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (zeta : Error) : Prop where
  incompletePartSelfConsistency :
    SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (incompletePartLeftFamily params family)
      (incompletePartRightFamily params family)
      zeta

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:560-720`
(`\label{lem:commutativity-switcheroo}`).

Lean statement for `lem:commutativity-switcheroo`. -/
structure CommutativitySwitcherooStatement {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (zeta omega chi : Error) : Prop where
  aggregateCommutation :
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (switcherooAggregateLeft params family M)
      (switcherooAggregateRight params family M)
      (commutativitySwitcherooError zeta omega chi)

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:721-774`
(`\label{cor:commuting-with-G-complete}`).

Lean statement for `cor:commuting-with-G-complete`. -/
structure CommutingWithGCompleteStatement (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) : Prop where
  pairwiseCompletePartCommutation :
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι) <|
          orderedProductOpFamily
            ((family.meas q.1).toSubMeas)
            ((family.meas q.2).toSubMeas))
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι) <|
          reversedProductOpFamily
            ((family.meas q.1).toSubMeas)
            ((family.meas q.2).toSubMeas))
      (pairwiseCompletePartCommutationError params gamma zeta)
  pointWithCompletePartCommutation :
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (completePartPointProductLeft params family)
      (completePartPointProductRight params family)
      (commutingWithGCompleteError params gamma zeta)
  completePartCommutation :
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (completePartTotalProductLeft params family)
      (completePartTotalProductRight params family)
      (commutingWithGCompleteError params gamma zeta)

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:775-816`
(`\label{cor:commuting-with-G-incomplete}`).

Lean statement for `cor:commuting-with-G-incomplete`. -/
structure CommutingWithGIncompleteStatement (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) : Prop where
  pointWithIncompletePartCommutation :
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (incompletePartPointProductLeft params family)
      (incompletePartPointProductRight params family)
      (commutingWithGIncompleteError params gamma zeta)
  incompletePartCommutation :
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (incompletePartTotalProductLeft params family)
      (incompletePartTotalProductRight params family)
      (commutingWithGIncompleteError params gamma zeta)

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:817-862`
(`\label{cor:G-hat-facts}`); the displayed `\widehat G` self-consistency and
commutation lines `eq:gselfconall` and `eq:gcomall` are at lines 821 and 823.

Lean statement for `cor:G-hat-facts`. -/
structure GHatFactsStatement (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) : Prop where
  completedSelfConsistency :
    SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta)
  completedCommutation :
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      (gHatCommutationError params gamma zeta)

end MIPStarRE.LDT.Pasting
