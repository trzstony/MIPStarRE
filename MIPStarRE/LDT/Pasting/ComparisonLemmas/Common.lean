import MIPStarRE.LDT.Commutativity.Main.Results
import MIPStarRE.LDT.Pasting.Core.CompletePart

/-!
# Section 12 pasting: comparison common helpers

Shared postprocessing, symmetry, distribution, boundedness, and arithmetic helpers for the Section
12 comparison lemmas.

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

lemma postprocess_postprocess
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (A : SubMeas α ι) (f : α → β) (g : β → γ) :
    postprocess (postprocess A f) g = postprocess A (g ∘ f) := by
  classical
  refine SubMeas.ext ?_ ?_
  · intro c
    simp [postprocess, Function.comp, Finset.sum_filter, Finset.sum_comm, eq_comm]
  · simp [postprocess_total]

lemma postprocess_hRestrictionToVerticalLine_eq_evaluateAt
    (params : Parameters) [FieldModel params.q]
    (H : SubMeas (Polynomial params.next) ι) (u : Point params.next) :
    postprocess
      (hRestrictionToVerticalLine params H (truncatePoint params u))
      (fun f => f (pointHeight params u)) =
    evaluateAt params.next u H := by
  let verticalLine : AxisParallelLine params.next :=
    { base := appendPoint params (truncatePoint params u) zeroCoord
      direction := lastCoord params }
  rw [show hRestrictionToVerticalLine params H (truncatePoint params u) =
      postprocess H (fun h => Polynomial.restrictToAxisParallelLine params.next h verticalLine) by
      rfl]
  rw [postprocess_postprocess]
  have happend : appendPoint params (truncatePoint params u) (pointHeight params u) = u := by
    exact (pointNextEquiv params).left_inv u
  have hbase : AxisParallelLine.pointAt verticalLine (pointHeight params u) = u := by
    calc
      AxisParallelLine.pointAt verticalLine (pointHeight params u)
        = appendPoint params (truncatePoint params u) (pointHeight params u) := by
            simpa [verticalLine] using
              verticalLine_pointAt_appendPoint params
                (truncatePoint params u) (pointHeight params u)
      _ = u := happend
  have hfun :
      (fun h =>
        (Polynomial.restrictToAxisParallelLine params.next h verticalLine)
          (pointHeight params u)) =
        fun h => h u := by
          funext h
          calc
            (Polynomial.restrictToAxisParallelLine params.next h verticalLine)
                (pointHeight params u)
              = h (AxisParallelLine.pointAt verticalLine (pointHeight params u)) :=
                  Polynomial.restrictToAxisParallelLine_apply params.next h verticalLine
                    (pointHeight params u)
            _ = h u := by simp [hbase]
  unfold evaluateAt
  refine congrArg (postprocess H) (funext fun h => ?_)
  change (Polynomial.restrictToAxisParallelLine params.next h verticalLine) (pointHeight params u)
      = h u
  exact congrFun hfun h

lemma consRel_uniform_fst
    {α β Outcome : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β] [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (A B : IdxSubMeas α Outcome ι) (δ : Error) :
    ConsRel ψ (uniformDistribution α) A B δ →
      ConsRel ψ (uniformDistribution (α × β))
        (fun ab => A ab.1)
        (fun ab => B ab.1)
        δ := by
  intro ⟨h⟩
  constructor
  unfold bipartiteConsError at *
  calc
    avgOver (uniformDistribution (α × β))
        (fun ab => qBipartiteConsDefect ψ (A ab.1) (B ab.1))
      = avgOver (uniformDistribution α)
          (fun a => qBipartiteConsDefect ψ (A a) (B a)) := by
            exact avgOver_uniform_fst (fun a => qBipartiteConsDefect ψ (A a) (B a))
    _ ≤ δ := h

end MIPStarRE.LDT.Pasting
