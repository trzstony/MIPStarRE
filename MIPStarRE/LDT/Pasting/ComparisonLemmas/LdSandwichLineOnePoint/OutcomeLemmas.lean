import MIPStarRE.LDT.Pasting.ComparisonLemmas.LdSandwichLineOnePoint.PrefixMoved

/-!
# Section 12 pasting: line one-point transport — outcome lemmas

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

/-- The postprocessed one-point right family has zero-operator `none` outcome,
because the selected slot satisfies `i < k` and is always postprocessed to `some`. -/
lemma ldSandwichLineOnePointRightFamily_outcome_none_eq_zero
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome none = 0 := by
  simp [ldSandwichLineOnePointRightFamily, postprocess, hi]

/-- The one-point right family is measurement-valued when the selected coordinate
exists.  This is the source of nonnegativity for the linear consistency defect. -/
lemma ldSandwichLineOnePointRightFamily_total_eq_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    ((ldSandwichLineOnePointRightFamily params strategy family k i) q).total = 1 := by
  let ℓ : AxisParallelLine params.next :=
    { base := appendPoint params q.1 zeroCoord
      direction := lastCoord params }
  simpa [ldSandwichLineOnePointRightFamily, verticalLineMeasurementFamily, hi,
    postprocess_total, ℓ] using (strategy.axisParallelMeasurement ℓ).total_eq_one

/-- The rotated prefix-only one-point left family has no `none` outcome. -/
lemma ldSandwichLineOnePointPrefixMovedFamily_outcome_none_eq_zero
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    (ldSandwichLineOnePointPrefixMovedFamily params family hi q).outcome none = 0 := by
  conv_lhs =>
    simp [ldSandwichLineOnePointPrefixMovedFamily, postprocess, restrictSubMeas,
      Finset.sum_filter]
  apply Finset.sum_eq_zero
  intro gs _hgs
  by_cases hsome : (gs 0).isSome = true
  · rcases Option.isSome_iff_exists.mp hsome with ⟨g, hg⟩
    simp [hg]
  · simp [hsome]

/-- Generic outcome expansion for evaluating a restricted completed-slice sandwich
family at a concrete field value. -/
lemma gHatSandwichFamily_restrict_eval_outcome_some
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {n : ℕ} (xs : PointTuple params n)
    (idx : Fin n) (u : Point params) (a : Fq params) :
    (postprocess
      (restrictSubMeas (gHatSandwichFamily params family n xs)
        (fun gs => (gs idx).isSome = true))
      (fun gs => Option.map (fun g : Polynomial params => g u) (gs idx))).outcome (some a) =
      ∑ gs : GHatTupleOutcome params n,
        if Option.map (fun g : Polynomial params => g u) (gs idx) = some a then
          let half := gHatHalfProductOutcomeOperator params family n xs gs
          half * halfᴴ
        else
          0 := by
  conv_lhs =>
    simp [postprocess, restrictSubMeas, gHatSandwichFamily, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro gs _hgs
  by_cases hmap : Option.map (fun g : Polynomial params => g u) (gs idx) = some a
  · rcases Option.map_eq_some_iff.mp hmap with ⟨g, hgs, hg⟩
    simp [hgs]
  · have hnone : ¬ ∃ g : Polynomial params, gs idx = some g ∧ g u = a := by
      rintro ⟨g, hgs, hg⟩
      exact hmap (Option.map_eq_some_iff.mpr ⟨g, hgs, hg⟩)
    simp [hnone]

/-- Outcome expansion for the original full one-point left family at a concrete field value. -/
lemma ldSandwichLineOnePointLeftFamily_outcome_some
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (a : Fq params) :
    ((ldSandwichLineOnePointLeftFamily params strategy family k i) q).outcome (some a) =
      ∑ gs : GHatTupleOutcome params k,
        if Option.map (fun g : Polynomial params => g q.1) (gs ⟨i, hi⟩) = some a then
          let half := gHatHalfProductOutcomeOperator params family k q.2 gs
          half * halfᴴ
        else
          0 := by
  simpa [ldSandwichLineOnePointLeftFamily, hi] using
    gHatSandwichFamily_restrict_eval_outcome_some
      params family q.2 ⟨i, hi⟩ q.1 a

/-- Outcome expansion for the original-order prefix family at a concrete field value. -/
lemma ldSandwichLineOnePointPrefixOriginalFamily_outcome_some
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (a : Fq params) :
    (ldSandwichLineOnePointPrefixOriginalFamily params family hi q).outcome (some a) =
      ∑ gs : GHatTupleOutcome params (i + 1),
        if Option.map (fun g : Polynomial params => g q.1)
            (gs ⟨i, Nat.lt_succ_self i⟩) = some a then
          let half := gHatHalfProductOutcomeOperator params family (i + 1)
            (fun j => q.2 ⟨j.1, by omega⟩) gs
          half * halfᴴ
        else
          0 := by
  simpa [ldSandwichLineOnePointPrefixOriginalFamily] using
    gHatSandwichFamily_restrict_eval_outcome_some
      params family (fun j => q.2 ⟨j.1, by omega⟩)
      ⟨i, Nat.lt_succ_self i⟩ q.1 a

/-- Outcome expansion for the selected-first prefix family at a concrete field value. -/
lemma ldSandwichLineOnePointPrefixMovedFamily_outcome_some
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (a : Fq params) :
    (ldSandwichLineOnePointPrefixMovedFamily params family hi q).outcome (some a) =
      ∑ gs : GHatTupleOutcome params (i + 1),
        if Option.map (fun g : Polynomial params => g q.1) (gs 0) = some a then
          let xsTail : PointTuple params i := fun j => q.2 ⟨j.1, by omega⟩
          let xs : PointTuple params (i + 1) := Fin.cons (q.2 ⟨i, hi⟩) xsTail
          let half := gHatHalfProductOutcomeOperator params family (i + 1) xs gs
          half * halfᴴ
        else
          0 := by
  simpa [ldSandwichLineOnePointPrefixMovedFamily] using
    gHatSandwichFamily_restrict_eval_outcome_some
      params family (Fin.cons (q.2 ⟨i, hi⟩) (fun j => q.2 ⟨j.1, by omega⟩))
      0 q.1 a

/-- The full one-point left family has no `none` outcome: the selected coordinate is
restricted to genuine completed polynomials before postprocessing by evaluation. -/
lemma ldSandwichLineOnePointLeftFamily_outcome_none_eq_zero
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    ((ldSandwichLineOnePointLeftFamily params strategy family k i) q).outcome none = 0 := by
  conv_lhs =>
    simp [ldSandwichLineOnePointLeftFamily, postprocess, restrictSubMeas, hi,
      Finset.sum_filter]
  apply Finset.sum_eq_zero
  intro gs _hgs
  cases hgs_i : gs ⟨i, hi⟩ with
  | none =>
      simp
  | some g =>
      simp

/-- The prefix-only one-point left family has no `none` outcome. -/
lemma ldSandwichLineOnePointPrefixOriginalFamily_outcome_none_eq_zero
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    (ldSandwichLineOnePointPrefixOriginalFamily params family hi q).outcome none = 0 := by
  conv_lhs =>
    simp [ldSandwichLineOnePointPrefixOriginalFamily, postprocess, restrictSubMeas,
      Finset.sum_filter]
  apply Finset.sum_eq_zero
  intro gs _hgs
  by_cases hsome : (gs ⟨i, Nat.lt_succ_self i⟩).isSome = true
  · rcases Option.isSome_iff_exists.mp hsome with ⟨g, hg⟩
    simp [hg]
  · simp [hsome]

/-- Delete one trailing sandwiched-line coordinate from the full one-point left
family, for a genuine field outcome.

This is the one-coordinate version of paper `ld-pasting.tex` lines 934--941:
summing over an extraneous completed-slice outcome collapses that measurement to
`I`, leaving the shorter sandwich. -/
lemma ldSandwichLineOnePointLeftFamily_drop_last_outcome_some
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {n i : ℕ} (hi : i < n)
    (q : SandwichedLineQuestion params (n + 1))
    (a : Fq params) :
    ((ldSandwichLineOnePointLeftFamily params strategy family (n + 1) i) q).outcome
        (some a) =
      ((ldSandwichLineOnePointLeftFamily params strategy family n i)
        (q.1, fun j => q.2 ⟨j.1, by omega⟩)).outcome (some a) := by
  let qPrefix : SandwichedLineQuestion params n := (q.1, fun j => q.2 ⟨j.1, by omega⟩)
  have hiFull : i < n + 1 := by omega
  rw [ldSandwichLineOnePointLeftFamily_outcome_some params strategy family hiFull q a]
  rw [ldSandwichLineOnePointLeftFamily_outcome_some params strategy family hi qPrefix a]
  let e := gHatTupleOutcomePrefixLastEquiv params n
  have hsplit :
      (∑ gs : GHatTupleOutcome params (n + 1),
        if Option.map (fun g : Polynomial params => g q.1) (gs ⟨i, hiFull⟩) = some a then
          let half := gHatHalfProductOutcomeOperator params family (n + 1) q.2 gs
          half * halfᴴ
        else
          0) =
      ∑ p : GHatTupleOutcome params n × GHatOutcome params,
        if Option.map (fun g : Polynomial params => g q.1) (p.1 ⟨i, hi⟩) = some a then
          let half := gHatHalfProductOutcomeOperator params family (n + 1) q.2 (e.symm p)
          half * halfᴴ
        else
          0 := by
    exact Fintype.sum_equiv e
      (fun gs : GHatTupleOutcome params (n + 1) =>
        if Option.map (fun g : Polynomial params => g q.1) (gs ⟨i, hiFull⟩) = some a then
          let half := gHatHalfProductOutcomeOperator params family (n + 1) q.2 gs
          half * halfᴴ
        else
          0)
      (fun p : GHatTupleOutcome params n × GHatOutcome params =>
        if Option.map (fun g : Polynomial params => g q.1) (p.1 ⟨i, hi⟩) = some a then
          let half := gHatHalfProductOutcomeOperator params family (n + 1) q.2 (e.symm p)
          half * halfᴴ
        else
          0)
      (by
        intro gs
        have hleft : e.symm (e gs) = gs := by
          exact e.left_inv gs
        rw [hleft]
        simp [e, gHatTupleOutcomePrefixLastEquiv])
  calc
    (∑ gs : GHatTupleOutcome params (n + 1),
        if Option.map (fun g : Polynomial params => g q.1) (gs ⟨i, hiFull⟩) = some a then
          let half := gHatHalfProductOutcomeOperator params family (n + 1) q.2 gs
          half * halfᴴ
        else
          0)
        = ∑ p : GHatTupleOutcome params n × GHatOutcome params,
            if Option.map (fun g : Polynomial params => g q.1) (p.1 ⟨i, hi⟩) = some a then
              let half := gHatHalfProductOutcomeOperator params family (n + 1) q.2 (e.symm p)
              half * halfᴴ
            else
              0 := hsplit
    _ = ∑ gsPrefix : GHatTupleOutcome params n,
          ∑ g : GHatOutcome params,
            if Option.map (fun g' : Polynomial params => g' q.1) (gsPrefix ⟨i, hi⟩) = some a then
              let half := gHatHalfProductOutcomeOperator params family (n + 1) q.2
                (e.symm (gsPrefix, g))
              half * halfᴴ
            else
              0 := by
          rw [← Finset.univ_product_univ, Finset.sum_product]
    _ = ∑ gsPrefix : GHatTupleOutcome params n,
          if Option.map (fun g : Polynomial params => g q.1) (gsPrefix ⟨i, hi⟩) = some a then
            let half := gHatHalfProductOutcomeOperator params family n qPrefix.2 gsPrefix
            half * halfᴴ
          else
            0 := by
          refine Finset.sum_congr rfl ?_
          intro gsPrefix _hgs
          by_cases hmatch : Option.map (fun g : Polynomial params => g q.1)
              (gsPrefix ⟨i, hi⟩) = some a
          · calc
              (∑ g : GHatOutcome params,
                if Option.map (fun g' : Polynomial params => g' q.1)
                    (gsPrefix ⟨i, hi⟩) = some a then
                  let half := gHatHalfProductOutcomeOperator params family (n + 1) q.2
                    (e.symm (gsPrefix, g))
                  half * halfᴴ
                else
                  0)
                  = ∑ g : GHatOutcome params,
                      let half := gHatHalfProductOutcomeOperator params family (n + 1) q.2
                        (e.symm (gsPrefix, g))
                      half * halfᴴ := by
                    simp [hmatch]
              _ = gHatHalfProductOutcomeOperator params family n qPrefix.2 gsPrefix *
                    (gHatHalfProductOutcomeOperator params family n qPrefix.2 gsPrefix)ᴴ := by
                    simpa [qPrefix, e] using
                      gHatSandwich_sum_last_eq_prefix params family n q.2 gsPrefix
              _ = if Option.map (fun g : Polynomial params => g q.1)
                    (gsPrefix ⟨i, hi⟩) = some a then
                    let half := gHatHalfProductOutcomeOperator params family n qPrefix.2 gsPrefix
                    half * halfᴴ
                  else
                    0 := by
                    simp [hmatch]
          · simp [hmatch]

/-- Deleting all coordinates after `i` from the full one-point left family leaves
exactly the prefix family used in the Cauchy--Schwarz transport.

This closes the paper's exact marginalization step `ld-pasting.tex` lines
932--953; the remaining analytic residual starts after this deletion. -/
lemma ldSandwichLineOnePointLeftFamily_eq_prefixOriginal
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) :
    ∀ {k i : ℕ} (hi : i < k),
      ldSandwichLineOnePointLeftFamily params strategy family k i =
        ldSandwichLineOnePointPrefixOriginalFamily params family hi
  | 0, i, hi => by cases hi
  | n + 1, i, hi => by
      by_cases hlast : i = n
      · subst i
        simpa using ldSandwichLineOnePointLeftFamily_self_eq_prefixOriginal
          params strategy family n
      · have hiPrefix : i < n := by omega
        have ih := ldSandwichLineOnePointLeftFamily_eq_prefixOriginal
          (params := params) (strategy := strategy) (family := family) hiPrefix
        funext q
        let qPrefix : SandwichedLineQuestion params n :=
          (q.1, fun j => q.2 ⟨j.1, by omega⟩)
        have hpref :
            ldSandwichLineOnePointPrefixOriginalFamily params family hiPrefix qPrefix =
              ldSandwichLineOnePointPrefixOriginalFamily params family hi q := by
          simp [ldSandwichLineOnePointPrefixOriginalFamily, qPrefix]
        have hout : ∀ o : Option (Fq params),
            ((ldSandwichLineOnePointLeftFamily params strategy family (n + 1) i) q).outcome o =
              (ldSandwichLineOnePointPrefixOriginalFamily params family hi q).outcome o := by
          intro o
          cases o with
          | none =>
              rw [ldSandwichLineOnePointLeftFamily_outcome_none_eq_zero
                params strategy family hi q]
              rw [ldSandwichLineOnePointPrefixOriginalFamily_outcome_none_eq_zero
                params family hi q]
          | some a =>
              calc
                ((ldSandwichLineOnePointLeftFamily params strategy family (n + 1) i) q).outcome
                    (some a)
                    = ((ldSandwichLineOnePointLeftFamily params strategy family n i)
                        qPrefix).outcome (some a) :=
                      ldSandwichLineOnePointLeftFamily_drop_last_outcome_some
                        params strategy family hiPrefix q a
                _ = (ldSandwichLineOnePointPrefixOriginalFamily params family hiPrefix
                        qPrefix).outcome (some a) := by
                      rw [congrFun ih qPrefix]
                _ = (ldSandwichLineOnePointPrefixOriginalFamily params family hi q).outcome
                        (some a) := by
                      rw [hpref]
        apply SubMeas.ext
        · exact hout
        · rw [← ((ldSandwichLineOnePointLeftFamily params strategy family (n + 1) i)
            q).sum_eq_total]
          rw [← (ldSandwichLineOnePointPrefixOriginalFamily params family hi q).sum_eq_total]
          exact Finset.sum_congr rfl fun o _ho => hout o

-- This arithmetic absorption proof expands several nested error estimates from the paper.

end MIPStarRE.LDT.Pasting
