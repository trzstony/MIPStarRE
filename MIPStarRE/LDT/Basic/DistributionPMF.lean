import MIPStarRE.LDT.Basic.DistributionUniformSums

/-!
# PMF expectations associated to project distributions

This module relates the uniform project `Distribution` average to the finite
expectation `PMF.realWeightedSum` on the Mathlib uniform probability mass
function.  The module-valued finite-sum algebra for uniform project
distributions lives in `MIPStarRE.LDT.Basic.DistributionUniformSums`.

## Main declarations

* `avgOver_uniform_eq_pmf_realWeightedSum`

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

/-- The uniform average is the finite expectation against Mathlib's uniform
probability mass function. -/
theorem avgOver_uniform_eq_pmf_realWeightedSum {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (f : α → Error) :
    avgOver (uniformDistribution α) f =
      PMF.realWeightedSum (PMF.uniformOfFintype α) f := by
  simpa [PMF.realWeightedSum, avgOver, smul_eq_mul] using
    uniformDistribution_sum_smul_eq_pmf_sum (α := α) (f := f)

end MIPStarRE.LDT
