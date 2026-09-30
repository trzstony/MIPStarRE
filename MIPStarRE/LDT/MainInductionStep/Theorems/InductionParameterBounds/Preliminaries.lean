import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import MIPStarRE.LDT.MainInductionStep.Defs
import MIPStarRE.LDT.Test.StrategyPolynomialFamilies
import MIPStarRE.LDT.Test.StrategyFailures

/-!
# Section 6 — Induction Parameter Bound Preliminaries

This file is one leaf of `InductionParameterBounds`. It contains the elementary
point-line reduction for the base case, the real-variable comparison lemmas used
by the small-parameter estimates, and the bound `d/q ≤ 1`.

## References

- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- At `m = 1`, `AxisParallelLine.throughPoint u i` does not depend on the
base point `u`: all axis-parallel lines in direction `i` are geometrically the
unique line and share the same canonical representative. -/
theorem throughPoint_eq_zeroPoint_of_m_eq_one
    (params : Parameters) [FieldModel params.q]
    (hm1 : params.m = 1)
    (u : Point params) (i : Fin params.m) :
    AxisParallelLine.throughPoint (params := params) u i =
      AxisParallelLine.throughPoint (params := params) zeroPoint i := by
  change
    ({ base := fun j => if j = i then zeroCoord else u j
       direction := i } : AxisParallelLine params) =
      { base := fun j => if j = i then zeroCoord else zeroPoint j
        direction := i }
  congr
  funext j
  haveI : Subsingleton (Fin params.m) := by
    rw [hm1]
    infer_instance
  have hji : j = i := Subsingleton.elim _ _
  simp [hji]

end MIPStarRE.LDT.MainInductionStep
