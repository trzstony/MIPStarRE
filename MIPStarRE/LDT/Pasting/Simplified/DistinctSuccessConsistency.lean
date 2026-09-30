import MIPStarRE.LDT.Pasting.Simplified.DistinctSuccessConstruction
import MIPStarRE.LDT.Pasting.ComparisonLemmas.LineInterpolation.BadLine

/-!
# Consistency witness for distinct-success interpolation

Two degree-bounded vertical-line polynomials that disagree differ at a
selected successful slice height. The first-success interpolant agrees
with the slice answer at every selected height, so a line mismatch produces
one of the single-position mismatches controlled by the pasting estimate.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of
  `lem:pasting-consistency`.
- `references/ldt-paper/ld-pasting.tex`, Section 12.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Restriction of the selected distinct-success interpolant to the
vertical line above `u`. -/
noncomputable def distinctSuccessVerticalLine
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (u : Point params)
    (xs : PointTuple params k) (gs : GHatTupleOutcome params k) :
    AxisLinePolynomial params.next :=
  Polynomial.restrictToAxisParallelLine params.next
    (distinctSuccessInterpolant params xs gs)
    ({ base := appendPoint params u zeroCoord
     , direction := lastCoord params } : AxisParallelLine params.next)

/-- A mismatch between the interpolant and another vertical-line answer
appears at one of the selected successful slice heights. -/
theorem distinctSuccessVerticalLine_ne_gives_selected_mismatch
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (u : Point params)
    (xs : PointTuple params k) (gs : GHatTupleOutcome params k)
    (h : HasDistinctSuccessSupport params xs gs)
    (f : AxisLinePolynomial params.next)
    (hne : distinctSuccessVerticalLine params u xs gs ≠ f) :
    ∃ i : Fin k, i ∈ distinctSuccessSupport params xs gs h ∧
      ∃ hiSome : (gs i).isSome = true,
        ((gs i).get hiSome) u ≠ f (xs i) := by
  let σ := distinctSuccessSupport params xs gs h
  obtain ⟨i, hiσ, hEvalNe⟩ :=
    axisLinePolynomial_ne_gives_support_eval_ne_injOn
      params xs σ (distinctSuccessSupport_injective params xs gs h)
      (distinctSuccessSupport_card params xs gs h) hne
  have hiSupport : i ∈ gHatTupleSupport gs :=
    distinctSuccessSupport_subset params xs gs h hiσ
  have hiSome : (gs i).isSome = true := by
    simpa [gHatTupleSupport] using hiSupport
  have hslicePoly :
      (Polynomial.restrictAtHeight params
        (distinctSuccessInterpolant params xs gs) (xs i)).poly =
        ((gs i).get hiSome).poly := by
    simpa [hiSome] using
      distinctSuccessInterpolant_restrictAtHeight params xs gs h hiσ
  have hsliceEval :
      (Polynomial.restrictAtHeight params
        (distinctSuccessInterpolant params xs gs) (xs i)) u =
        ((gs i).get hiSome) u := by
    simpa [Polynomial.toFun, evalPolynomialModel] using congrArg
      (fun p : PolynomialModel params =>
        encodeScalar (MvPolynomial.eval (decodePoint u) p)) hslicePoly
  have hlineEval :
      distinctSuccessVerticalLine params u xs gs (xs i) =
        ((gs i).get hiSome) u := by
    calc
      distinctSuccessVerticalLine params u xs gs (xs i) =
          (Polynomial.restrictAtHeight params
            (distinctSuccessInterpolant params xs gs) (xs i)) u := by
            simpa [distinctSuccessVerticalLine] using
              restrictToVerticalLine_eval_eq_restrictAtHeight_eval
                params (distinctSuccessInterpolant params xs gs) u (xs i)
      _ = ((gs i).get hiSome) u := hsliceEval
  refine ⟨i, hiσ, hiSome, ?_⟩
  exact fun heq => hEvalNe (by rw [hlineEval]; exact heq)

end MIPStarRE.LDT.Pasting
