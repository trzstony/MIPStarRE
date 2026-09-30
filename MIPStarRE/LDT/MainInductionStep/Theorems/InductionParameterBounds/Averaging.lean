import MIPStarRE.LDT.Basic.DistributionPMF
import MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds.Preliminaries

/-!
# Section 6 — Jensen estimate for averaged slice errors

This file contains the uniform Jensen estimate for fractional powers used to
bound the average of the slice errors in the induction step.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-induction`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

/-- Jensen's inequality for `Real.rpow (1/n)` against a uniform distribution:
the average of `(f a)^{1/n}` is at most `(average f)^{1/n}`. This is the
workhorse used inside each of the averaged-slice bounds (`average_slice…_le`)
to push `rpow (1/32)` or `rpow (1/1024)` through a uniform `avgOver` on
`Fq params`. -/
lemma avgOver_uniform_rpow_one_div_le_rpow_avg
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (f : α → Error) (n : ℕ) (hn : 1 ≤ n) (hf : ∀ a, 0 ≤ f a) :
    avgOver (uniformDistribution α)
        (fun a => Real.rpow (f a) (1 / (n : Error))) ≤
      Real.rpow (avgOver (uniformDistribution α) f) (1 / (n : Error)) := by
  rw [avgOver_uniform_eq_pmf_realWeightedSum, avgOver_uniform_eq_pmf_realWeightedSum]
  exact PMF.realWeightedSum_rpow_one_div_le_rpow
    (p := PMF.uniformOfFintype α) (f := f) (n := n) hn hf

end MIPStarRE.LDT.MainInductionStep
