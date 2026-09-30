import MIPStarRE.LDT.Pasting.ComparisonLemmas.LdSandwichLineOnePoint.OutcomeLemmas

/-!
# Section 12 pasting: line one-point transport — Cauchy-Schwarz setup

Internal helper module; part of the file-split for `#1127`.

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

/-- The linear (pre-`max`) form of the bipartite consistency defect.

Internal helper for the `LdSandwichLineOnePoint` Cauchy--Schwarz setup;
exposed for a future file-split (`#1127`). -/
noncomputable def qBipartiteLinearConsDefect {Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : SubMeas Outcome ιA) (B : SubMeas Outcome ιB) : Error :=
  ev ψ (opTensor A.total B.total) - qBipartiteMatchMass ψ A B

/-- For option-valued families with no `none` mass, the linear bipartite
consistency defect is the paper's sum against the complementary right outcome.

This is the bookkeeping step that rewrites
`⟨ψ|A_total ⊗ B_total|ψ⟩ - Σ_o ⟨ψ|A_o ⊗ B_o|ψ⟩` as
`Σ_a ⟨ψ|A_a ⊗ (I - B_a)|ψ⟩` when Bob's family is a measurement and both
`none` outcomes vanish.

Internal helper for the `LdSandwichLineOnePoint` Cauchy--Schwarz setup;
exposed for a future file-split (`#1127`). -/
lemma qBipartiteLinearConsDefect_option_eq_sum_some_complement
    {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB))
    (A : SubMeas (Option α) ιA) (B : SubMeas (Option α) ιB)
    (hBtotal : B.total = 1)
    (hAnone : A.outcome none = 0) (hBnone : B.outcome none = 0) :
    qBipartiteLinearConsDefect ψ A B =
      ∑ a : α, ev ψ (opTensor (A.outcome (some a)) (1 - B.outcome (some a))) := by
  classical
  have htotal_sum :
      ev ψ (opTensor A.total B.total) =
        ∑ o : Option α, ev ψ (opTensor (A.outcome o) (1 : MIPStarRE.Quantum.Op ιB)) := by
    calc
      ev ψ (opTensor A.total B.total)
          = ev ψ (opTensor A.total (1 : MIPStarRE.Quantum.Op ιB)) := by
            rw [hBtotal]
      _ = ev ψ (opTensor (∑ o : Option α, A.outcome o)
            (1 : MIPStarRE.Quantum.Op ιB)) := by
            rw [A.sum_eq_total]
      _ = ev ψ (∑ o : Option α,
            opTensor (A.outcome o) (1 : MIPStarRE.Quantum.Op ιB)) := by
            rw [opTensor_sum_left_univ]
      _ = ∑ o : Option α, ev ψ (opTensor (A.outcome o)
            (1 : MIPStarRE.Quantum.Op ιB)) := by
            rw [ev_sum]
  have hdiff_sum :
      ev ψ (opTensor A.total B.total) - qBipartiteMatchMass ψ A B =
        ∑ o : Option α, ev ψ (opTensor (A.outcome o) (1 - B.outcome o)) := by
    rw [htotal_sum]
    unfold qBipartiteMatchMass
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro o _ho
    rw [← ev_sub]
    congr 1
    simpa [opTensor] using (MIPStarRE.Quantum.kronecker_sub_right
      (A := A.outcome o)
      (B₁ := (1 : MIPStarRE.Quantum.Op ιB))
      (B₂ := B.outcome o))
  unfold qBipartiteLinearConsDefect
  rw [hdiff_sum]
  rw [Fintype.sum_option]
  simp [hAnone, hBnone, opTensor, ev_zero]

/-- The linear consistency defect is nonnegative when the right-hand family is a
measurement.  This lets the paper's averaged linear estimate feed the `max 0`
`qBipartiteConsDefect` maximum form without needing a pointwise absolute-value gap.

Internal helper for the `LdSandwichLineOnePoint` Cauchy--Schwarz setup;
exposed for a future file-split (`#1127`). -/
lemma qBipartiteLinearConsDefect_nonneg_of_right_total_one
    {Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : SubMeas Outcome ιA) (B : SubMeas Outcome ιB)
    (hBtotal : B.total = 1) :
    0 ≤ qBipartiteLinearConsDefect ψ A B := by
  have hmatch_le_left :
      qBipartiteMatchMass ψ A B ≤ ev ψ (leftTensor (ι₂ := ιB) A.total) := by
    unfold qBipartiteMatchMass
    calc
      (∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a)))
          ≤ ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ιB) (A.outcome a)) := by
            refine Finset.sum_le_sum ?_
            intro a _ha
            exact ev_mono ψ _ _ <|
              opTensor_le_leftTensor (ι₂ := ιB)
                (A.outcome_pos a) (SubMeas.outcome_le_one B a)
      _ = ev ψ (leftTensor (ι₂ := ιB) A.total) := by
            rw [← ev_sum ψ (fun a : Outcome => leftTensor (ι₂ := ιB) (A.outcome a))]
            rw [leftTensor_finset_sum (ι₂ := ιB) Finset.univ A.outcome]
            rw [A.sum_eq_total]
  have hleft_eq :
      ev ψ (leftTensor (ι₂ := ιB) A.total) = ev ψ (opTensor A.total B.total) := by
    simp [hBtotal, leftTensor, opTensor]
  unfold qBipartiteLinearConsDefect
  linarith

/-- The original expanded off-diagonal scalar in `ld-pasting.tex:960--963`.

This is the source side after deleting extraneous tail coordinates and expanding
the linear consistency defect as `Σ_a ⟨ψ|A_a ⊗ (I-B_a)|ψ⟩`. -/
noncomputable def ldSandwichLineOnePoint_prefix_sourceOutcomeSum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) : Error :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ a : Fq params,
      ev strategy.state
        (opTensor
          (((ldSandwichLineOnePointPrefixOriginalFamily params family hi) q).outcome
            (some a))
          (1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
            (some a))))

/-- The intermediate scalar after the first Cauchy--Schwarz move
`ld-pasting.tex:964--986` (`eq:gonna-need-a-bigger-cauchy-schwarz`).

For an original-order prefix outcome `gs`, `orderedHalf` is
`G^{x_<i}_{g_<i} G^{x_i}_{g_i}` while `rotatedHalf` is
`G^{x_i}_{g_i} G^{x_<i}_{g_<i}`.  The first CS move replaces only the left half
of the sandwich, leaving `orderedHalf†` on the right. -/
noncomputable def ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) : Error :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ gs : GHatTupleOutcome params (i + 1),
      match Option.map (fun g : Polynomial params => g q.1)
          (gs ⟨i, Nat.lt_succ_self i⟩) with
      | none => 0
      | some a =>
          let orderedHalf := gHatHalfProductOutcomeOperator params family (i + 1)
            (fun j => q.2 ⟨j.1, by omega⟩) gs
          let rotatedHalf := gHatHalfProductOutcomeOperator params family (i + 1)
            ((pointTupleLastFrontEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))
            ((gHatTupleOutcomeLastFrontEquiv params i) gs)
          ev strategy.state
            (opTensor (rotatedHalf * orderedHalfᴴ)
              (1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
                (some a))))

/-- The target expanded off-diagonal scalar after the two CS moves.

This is the moved-prefix side; the endpoint/prefix-completeness collapse is
`ldSandwichLineOnePointPrefixMoved_eq_endpoint`, corresponding to
`ld-pasting.tex:1011--1024`. -/
noncomputable def ldSandwichLineOnePoint_prefix_movedOutcomeSum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) : Error :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ a : Fq params,
      ev strategy.state
        (opTensor
          (((ldSandwichLineOnePointPrefixMovedFamily params family hi) q).outcome
            (some a))
          (1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
            (some a))))

/-- Ordered half-product appearing in the line-one-point CS step. -/
noncomputable def ldSandwichLineOnePointCS_orderedHalf
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (gs : GHatTupleOutcome params (i + 1)) : MIPStarRE.Quantum.Op ι :=
  gHatHalfProductOutcomeOperator params family (i + 1)
    (fun j => q.2 ⟨j.1, by omega⟩) gs

/-- Rotated half-product appearing after moving the selected slice to the front. -/
noncomputable def ldSandwichLineOnePointCS_rotatedHalf
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (gs : GHatTupleOutcome params (i + 1)) : MIPStarRE.Quantum.Op ι :=
  gHatHalfProductOutcomeOperator params family (i + 1)
    ((pointTupleLastFrontEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))
    ((gHatTupleOutcomeLastFrontEquiv params i) gs)

/-- Right-hand complement selected by the completed polynomial outcome. -/
noncomputable def ldSandwichLineOnePointCS_rightComplement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ}
    (q : SandwichedLineQuestion params k)
    (gs : GHatTupleOutcome params (i + 1)) : MIPStarRE.Quantum.Op ι :=
  match Option.map (fun g : Polynomial params => g q.1)
      (gs ⟨i, Nat.lt_succ_self i⟩) with
  | none => 0
  | some a =>
      1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome (some a)

end MIPStarRE.LDT.Pasting
