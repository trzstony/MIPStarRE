import MIPStarRE.LDT.Pasting.ComparisonLemmas.LineInterpolation.BadMass
import MIPStarRE.LDT.Pasting.ComparisonLemmas.LineInterpolation.Averaging
import MIPStarRE.LDT.Pasting.ComparisonLemmas.LdSandwichLineOnePoint.CSSetup
import MIPStarRE.LDT.Pasting.Core.DDistinct

/-!
# Line interpolation: H-B consistency error aggregation

Fixed-`u` defect, `hBConsistencyError`, degree-ratio error bounds,
and the final bad-mass aggregation lemma that drives `lem:h-b-consistency`.

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

lemma avgOver_sum_fin
    {α : Type*} (𝒟 : Distribution α) (k : ℕ) (f : α → Fin k → Error) :
    avgOver 𝒟 (fun a => ∑ i : Fin k, f a i) =
      ∑ i : Fin k, avgOver 𝒟 (fun a => f a i) :=
  avgOver_sum 𝒟 f

end MIPStarRE.LDT.Pasting
