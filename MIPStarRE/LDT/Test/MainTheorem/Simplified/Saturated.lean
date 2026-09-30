import MIPStarRE.LDT.Test.MainTheorem.Simplified.Statements

/-!
# Saturated-error branch of the final theorem

When the error parameter is at least one, complete projective polynomial
measurements supported on a fixed polynomial satisfy all three conclusions of
`thm:main-formal`, because every bipartite consistency defect for a normalized
state and a uniform question distribution is at most one.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-formal`,
  first paragraph.
-/

namespace MIPStarRE.LDT.Test

/-- The three conclusions of `thm:main-formal` hold at every error `ν ≥ 1`.
The argument does not use the low individual degree test hypothesis. -/
theorem mainFormalConclusion_of_one_le
    (params : Parameters) [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    {ν : Error} (hν : 1 ≤ ν) :
    MainFormalConclusion params strategy ν := by
  classical
  haveI : Inhabited (Polynomial params) :=
    ⟨⟨0, by intro i; simp [MvPolynomial.degreeOf_zero]⟩⟩
  let trivialA : ProjMeas (Polynomial params) ιA :=
    ProjMeas.trivialDistinguishedOutcome (default : Polynomial params)
  let trivialB : ProjMeas (Polynomial params) ιB :=
    ProjMeas.trivialDistinguishedOutcome (default : Polynomial params)
  refine ⟨trivialA, trivialB, ?_, ?_, ?_⟩
  all_goals exact ⟨le_trans
    (bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized _ _) hν⟩

end MIPStarRE.LDT.Test
