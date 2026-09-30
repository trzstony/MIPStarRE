import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.MoveLemmas.Basic

/-!
# Section 12 pasting: scalar bounds for complementary Bernoulli branches

This file collects the elementary scalar estimates used by the complementary
branches of `thm:ld-pasting`.  These estimates correspond to the large-error
reduction in `references/ldt-paper/ld-pasting.tex`, lines 52--55.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The scalar `κ` in a complete family is nonnegative. -/
lemma kappa_nonneg_of_complete
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {kappa : Error}
    (hcomplete : family.Complete strategy.state kappa) :
    0 ≤ kappa := by
  have hmass_le_one : subMeasMass strategy.state family.averagedSubMeas.liftLeft ≤ 1 := by
    unfold subMeasMass SubMeas.liftLeft
    have hle : leftTensor (ι₂ := ι) (IdxPolyFamily.averagedSubMeas family).total ≤
        (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
      exact leftTensor_le_one (ι₂ := ι) (IdxPolyFamily.averagedSubMeas family).total_le_one
    simpa [ev_one_of_isNormalized strategy.state strategy.isNormalized] using
      ev_mono strategy.state _ _ hle
  have hlower := hcomplete.averageCompleteness.lowerBound
  linarith

end MIPStarRE.LDT.Pasting
