import MIPStarRE.LDT.Pasting.ComparisonLemmas.LineInterpolation.Core

/-!
# Line interpolation: bad-line event

Definitions and lemmas for `tupleInterpolatedVerticalLine` and mismatch
extraction in the line-interpolation argument.

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

lemma evaluateAt_averageIdxSubMeas
    (params : Parameters) [FieldModel params.q]
    {Question : Type*}
    (u : Point params)
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question (Polynomial params) ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    evaluateAt params u (averageIdxSubMeas 𝒟 A h𝒟) =
      averageIdxSubMeas 𝒟 (fun q => evaluateAt params u (A q)) h𝒟 := by
  classical
  refine SubMeas.ext ?_ ?_
  · intro a
    simp [evaluateAt, postprocess, averageIdxSubMeas, averageOperatorOverDistribution,
      Finset.sum_filter, Finset.sum_comm, Finset.smul_sum]
  · simp [evaluateAt, postprocess, averageIdxSubMeas, averageOperatorOverDistribution]

lemma hRestrictionToVerticalLine_averageIdxSubMeas
    (params : Parameters) [FieldModel params.q]
    {Question : Type*}
    (u : Point params)
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question (Polynomial params.next) ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    hRestrictionToVerticalLine params (averageIdxSubMeas 𝒟 A h𝒟) u =
      averageIdxSubMeas 𝒟 (fun q => hRestrictionToVerticalLine params (A q) u) h𝒟 := by
  classical
  refine SubMeas.ext ?_ ?_
  · intro f
    simp [hRestrictionToVerticalLine, postprocess, averageIdxSubMeas,
      averageOperatorOverDistribution, Finset.sum_filter, Finset.sum_comm,
      Finset.smul_sum]
  · simp [hRestrictionToVerticalLine, postprocess, averageIdxSubMeas,
      averageOperatorOverDistribution]

end MIPStarRE.LDT.Pasting
