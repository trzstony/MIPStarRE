import MIPStarRE.LDT.Basic.DistributionAvg

/-!
# Product rules for finite-support distribution averages

This module contains product and marginalization rules for operator-valued
uniform averages.  The scalar product rules, together with the common
PMF-weighted finite-sum identities on which both scalar and operator rules
depend, are in `MIPStarRE.LDT.Basic.DistributionUniformSums` and
`MIPStarRE.LDT.Basic.PMFAverages`.

## Main definitions / statements

* `averageOperatorOverDistribution_uniform_prod`
* `averageOperatorOverDistribution_uniform_comm`
* `averageOperatorOverDistribution_uniform_prod_swap`
* `averageOperatorOverDistribution_uniform_fst`
* `averageOperatorOverDistribution_uniform_snd`
* `averageOperatorOverDistribution_uniform_equiv_prod`
* `averageOperatorOverDistribution_uniform_equiv_prod_swap`
* `averageOperatorOverDistribution_uniform_equiv_fst`
* `averageOperatorOverDistribution_uniform_equiv_snd`

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

/-- Transport a uniform operator average through an equivalence whose target is
a product, then split the product average into iterated uniform averages. -/
theorem averageOperatorOverDistribution_uniform_equiv_prod
    {γ α β : Type*}
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : γ ≃ α × β) (f : γ → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution (uniformDistribution γ) f =
      averageOperatorOverDistribution (uniformDistribution α)
        (fun a => averageOperatorOverDistribution (uniformDistribution β)
          (fun b => f (e.symm (a, b)))) := by
  simpa [averageOperatorOverDistribution] using
    uniformDistribution_sum_smul_equiv_prod (e := e) (f := f)

end MIPStarRE.LDT
