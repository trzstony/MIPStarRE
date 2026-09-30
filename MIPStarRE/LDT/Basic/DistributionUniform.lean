import MIPStarRE.LDT.Basic.DistributionAvg

/-!
# Uniform subset estimates

This file contains estimates for the total variation distance between the
uniform distribution on a finite type and the uniform distribution on a
nonempty finite subset, together with averaging bounds for `[0,1]`-valued
functions.  The uniform-subset total-variation identity is proved by transport
through Mathlib probability mass functions.
-/

open scoped BigOperators

namespace MIPStarRE.LDT

/-- Total variation between the uniform distribution on a finite ambient type and
the uniform distribution on a nonempty finite subset.

This is the elementary finite identity
`TV(uniform α, uniform s) = 1 - |s| / |α|`.  The proof transports the project
`Distribution` statement to Mathlib's uniform probability mass functions. -/
theorem totalVariationDistance_uniformDistribution_uniformOnFinset_eq
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (s : Finset α) (hs : s.Nonempty) :
    totalVariationDistance (uniformDistribution α) (Distribution.uniformOnFinset s) =
      1 - (s.card : Error) / (Fintype.card α : Error) := by
  rw [totalVariationDistance_eq_toPMF_sum]
  change PMF.totalVariationDistance
      ((uniformDistribution α).toPMF (uniformDistribution_isProbability α))
      ((Distribution.uniformOnFinset s).toPMF
        (Distribution.uniformOnFinset_isProbability s hs)) =
    1 - (s.card : Error) / (Fintype.card α : Error)
  rw [uniformDistribution_toPMF, Distribution.uniformOnFinset_toPMF]
  exact PMF.totalVariationDistance_uniformOfFintype_uniformOfFinset_eq s hs

end MIPStarRE.LDT
