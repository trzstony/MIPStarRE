import MIPStarRE.LDT.Pasting.Simplified.MarginalStability

/-!
# Marginal stability of completed measurement words

The two tensor placements of a completed word each form a normalized
operator family. Their squared distance is the random-word mirror energy,
so the general effect-stability inequality applies without a loss in the
number of word outcomes.

## References

- `blueprint/src/low_degree_simplified.tex`,
  `lem:sequential-bot-marginal`.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A completed word acting on the first register. -/
noncomputable def completedWordLeft
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (xs : PointTuple params k) (gs : GHatTupleOutcome params k) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  leftTensor (ι₂ := ι) (gHatHalfProductOutcomeOperator params family k xs gs)

/-- The adjoint completed word acting on the second register. -/
noncomputable def completedWordRight
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (xs : PointTuple params k) (gs : GHatTupleOutcome params k) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  rightTensor (ι₁ := ι)
    (gHatHalfProductOutcomeOperator params family k xs gs)ᴴ

/-- The family squared distance is the random-word mirror energy. -/
theorem completedWord_distance_eq_energy
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (ψ : QuantumState (ι × ι)) :
    averagedOperatorNormSq ψ (uniformDistribution (PointTuple params k))
      (fun xs gs => completedWordLeft params family k xs gs -
        completedWordRight params family k xs gs) =
      ev ψ (randomWordMirrorEnergy params family k) := by
  unfold randomWordMirrorEnergy
  rw [ev_averageOperatorOverDistribution]
  unfold averagedOperatorNormSq
  apply avgOver_congr
  intro xs
  rw [ev_finset_sum]
  rfl

end MIPStarRE.LDT.Pasting
