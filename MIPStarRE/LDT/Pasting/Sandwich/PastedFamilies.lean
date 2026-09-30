import MIPStarRE.LDT.CommutativityPoints.Approximation
import MIPStarRE.LDT.Pasting.Sandwich.GHatSandwich

/-!
# Section 12 — vertical-line families

The vertical-line measurement family `B^u` of the strategy in the last
coordinate, its lift to the answer type of the slice measurements, the
restriction of a global polynomial to a vertical line, and the left and right
families of the line one-point transport used by the pasting consistency
estimate.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Placeholder family for the vertical axis-parallel line measurement `B^u_f`. -/
noncomputable def verticalLineMeasurementFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    IdxSubMeas (VerticalLineQuestion params) (AxisLinePolynomial params.next) ι :=
  fun u =>
    let ℓ : AxisParallelLine params.next :=
      { base := appendPoint params u zeroCoord
        direction := lastCoord params }
    (strategy.axisParallelMeasurement ℓ).toSubMeas

/-- The canonical vertical line through `u : Point params` reaches `appendPoint u x`
at parameter `x`. -/
theorem verticalLine_pointAt_appendPoint
    (params : Parameters) [FieldModel params.q]
    (u : Point params) (x : Fq params) :
    ({ base := appendPoint params u zeroCoord,
       direction := lastCoord params } : AxisParallelLine params.next).pointAt x =
      appendPoint params u x := by
  ext i
  by_cases hlast : i = lastCoord params
  · subst i
    have hzero :
        addCoord (params := params.next) (zeroCoord (params := params)) x = x := by
      change addCoord (params := params) zeroCoord x = x
      unfold addCoord zeroCoord
      rw [decode_encodeScalar]
      simp
    simpa [AxisParallelLine.pointAt, appendPoint, lastCoord,
      Nat.lt_irrefl] using congrArg Fin.val hzero
  · have him : i.1 < params.m := by
      have hi_lt : i.1 < params.m + 1 := by simpa [Parameters.next] using i.2
      by_cases hlt : i.1 < params.m
      · exact hlt
      · have hi_eq : i.1 = params.m := by omega
        have hi_last : i = lastCoord params := by
          apply Fin.ext
          simp [lastCoord, hi_eq]
        exact (hlast hi_last).elim
    simp [AxisParallelLine.pointAt, appendPoint, him, hlast]

/-- Pull back the vertical-line answer family along `truncatePoint`, then read
its line polynomial at the lifted point's final coordinate. -/
noncomputable def liftedVerticalLineAnswerFamily
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    IdxSubMeas (Point params.next) (Fq params) ι :=
  fun u =>
    postprocess
      (verticalLineMeasurementFamily params strategy (truncatePoint params u))
      (fun f => f (pointHeight params u))

/-- Explicit value extracted from the `i`-th genuine slice outcome at the test point.

The paper's one-point sandwich comparison only sums over tuples with
`g_i ≠ ⊥`; the `none` mass is therefore removed before postprocessing. -/
noncomputable def ldSandwichLineOnePointLeftFamily (params : Parameters) [FieldModel params.q]
    (_strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (k i : ℕ) : IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) ι :=
  fun q =>
    postprocess
      (restrictSubMeas (gHatSandwichFamily params family k q.2)
        (fun gs => if h : i < k then (gs ⟨i, h⟩).isSome = true else False))
      (fun gs => if h : i < k then Option.map (fun g => g q.1) (gs ⟨i, h⟩) else none)

/-- Explicit value extracted from the vertical line measurement `B^u` at the slice height `x_i`. -/
noncomputable def ldSandwichLineOnePointRightFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (_family : IdxPolyFamily params ι)
    (k i : ℕ) : IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) ι :=
  fun q =>
    postprocess (verticalLineMeasurementFamily params strategy q.1) (fun f =>
      if h : i < k then
        some (f (q.2 ⟨i, h⟩))
      else
        none)

/-- Restrict a global polynomial-valued submeasurement to the vertical line through `u`. -/
noncomputable def hRestrictionToVerticalLine (params : Parameters) [FieldModel params.q]
    (H : SubMeas (Polynomial params.next) ι) :
    IdxSubMeas (VerticalLineQuestion params) (AxisLinePolynomial params.next) ι :=
  fun u =>
    let verticalLine : AxisParallelLine params.next :=
      { base := appendPoint params u zeroCoord
        direction := ⟨params.m, Nat.lt_succ_self params.m⟩ }
    postprocess H (fun h => Polynomial.restrictToAxisParallelLine params.next h verticalLine)

end MIPStarRE.LDT.Pasting
