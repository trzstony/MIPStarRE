import MIPStarRE.LDT.Pasting.Sandwich.GHatFamilies

/-!
# Section 12 — Sandwich constructions: `GHat` sandwich families

Completed-slice sandwich families and restriction helpers.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Concrete family for the full sandwich
`\widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k} \cdots \widehat G^{x_1}_{g_1}`. -/
noncomputable def gHatSandwichFamily (params : Parameters) [FieldModel.{v} params.q]
    (family : IdxPolyFamily.{u, v} params ι) (k : ℕ) :
    IdxSubMeas.{0, v, u} (PointTuple params k) (GHatTupleOutcome params k) ι :=
  fun xs => by
    refine
    { outcome := fun gs =>
        let half := gHatHalfProductOutcomeOperator params family k xs gs
        half * halfᴴ
      total :=
        let half := gHatHalfProductTotalOperator params family k xs
        half * halfᴴ
      outcome_pos := ?_
      sum_eq_total := ?_
      total_le_one := ?_ }
    · intro gs
      simpa using
        (Matrix.posSemidef_self_mul_conjTranspose
          (gHatHalfProductOutcomeOperator params family k xs gs)).nonneg
    · induction k with
      | zero =>
          simp [gHatHalfProductOutcomeOperator, gHatHalfProductTotalOperator]
      | succ k ih =>
          let α := fun _ : Fin (k + 1) => GHatOutcome params
          have hsplit :
              (∑ gs : GHatTupleOutcome params (k + 1),
                  let half := gHatHalfProductOutcomeOperator params family (k + 1) xs gs
                  half * halfᴴ) =
                ∑ p : GHatOutcome params × GHatTupleOutcome params k,
                  (gHatIdxMeas params family (xs 0)).outcome p.1 *
                    (gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) p.2 *
                      (gHatHalfProductOutcomeOperator
                        params family k (pointTupleTail xs) p.2)ᴴ) *
                    (gHatIdxMeas params family (xs 0)).outcome p.1 := by
            symm
            exact Fintype.sum_equiv (Fin.consEquiv α)
              (fun p =>
                (gHatIdxMeas params family (xs 0)).outcome p.1 *
                  (gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) p.2 *
                    (gHatHalfProductOutcomeOperator
                      params family k (pointTupleTail xs) p.2)ᴴ) *
                  (gHatIdxMeas params family (xs 0)).outcome p.1)
              (fun gs =>
                let half := gHatHalfProductOutcomeOperator params family (k + 1) xs gs
                half * halfᴴ)
              (by
                intro p
                have htail :
                    gHatTupleOutcomeTail ((Fin.consEquiv α) p) = p.2 := by
                  funext i
                  rfl
                simp [gHatHalfProductOutcomeOperator, htail,
                  Matrix.conjTranspose_mul,
                  Matrix.mul_assoc, (gHatIdxMeas params family (xs 0)).outcome_hermitian])
          rw [hsplit]
          rw [← Finset.univ_product_univ, Finset.sum_product]
          calc
            ∑ g : GHatOutcome params,
                ∑ gs : GHatTupleOutcome params k,
                  (gHatIdxMeas params family (xs 0)).outcome g *
                    (gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) gs *
                      (gHatHalfProductOutcomeOperator
                        params family k (pointTupleTail xs) gs)ᴴ) *
                    (gHatIdxMeas params family (xs 0)).outcome g
              = ∑ g : GHatOutcome params,
                  (gHatIdxMeas params family (xs 0)).outcome g *
                    (∑ gs : GHatTupleOutcome params k,
                      gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) gs *
                        (gHatHalfProductOutcomeOperator
                          params family k (pointTupleTail xs) gs)ᴴ) *
                    (gHatIdxMeas params family (xs 0)).outcome g := by
                  refine Finset.sum_congr rfl ?_
                  intro g _hg
                  calc
                    ∑ gs : GHatTupleOutcome params k,
                        (gHatIdxMeas params family (xs 0)).outcome g *
                          (gHatHalfProductOutcomeOperator
                            params family k (pointTupleTail xs) gs *
                            (gHatHalfProductOutcomeOperator
                              params family k (pointTupleTail xs) gs)ᴴ) *
                          (gHatIdxMeas params family (xs 0)).outcome g
                      = (∑ gs : GHatTupleOutcome params k,
                          (gHatIdxMeas params family (xs 0)).outcome g *
                            (gHatHalfProductOutcomeOperator
                              params family k (pointTupleTail xs) gs *
                              (gHatHalfProductOutcomeOperator
                                params family k (pointTupleTail xs) gs)ᴴ)) *
                          (gHatIdxMeas params family (xs 0)).outcome g := by
                            rw [Finset.sum_mul]
                      _ = (gHatIdxMeas params family (xs 0)).outcome g *
                            (∑ gs : GHatTupleOutcome params k,
                              gHatHalfProductOutcomeOperator
                                params family k (pointTupleTail xs) gs *
                                (gHatHalfProductOutcomeOperator
                                  params family k (pointTupleTail xs) gs)ᴴ) *
                            (gHatIdxMeas params family (xs 0)).outcome g := by
                            rw [Matrix.mul_sum]
            _ = ∑ g : GHatOutcome params,
                  (gHatIdxMeas params family (xs 0)).outcome g *
                    (gHatHalfProductTotalOperator params family k (pointTupleTail xs) *
                      (gHatHalfProductTotalOperator
                        params family k (pointTupleTail xs))ᴴ) *
                    (gHatIdxMeas params family (xs 0)).outcome g := by
                  refine Finset.sum_congr rfl ?_
                  intro g _hg
                  rw [ih (pointTupleTail xs)]
            _ = ∑ g : GHatOutcome params,
                  (gHatIdxMeas params family (xs 0)).outcome g * 1 *
                    (gHatIdxMeas params family (xs 0)).outcome g := by
                  refine Finset.sum_congr rfl ?_
                  intro g _hg
                  simp [gHatHalfProductTotalOperator_eq_one]
            _ = ∑ g : GHatOutcome params,
                  (gHatIdxMeas params family (xs 0)).outcome g *
                    (gHatIdxMeas params family (xs 0)).outcome g := by
                  simp
            _ = ∑ g : GHatOutcome params, (gHatIdxMeas params family (xs 0)).outcome g := by
                  refine Finset.sum_congr rfl ?_
                  intro g _hg
                  exact gHatIdxMeas_proj params family (xs 0) g
            _ = (gHatIdxMeas params family (xs 0)).total := by
                  rw [(gHatIdxMeas params family (xs 0)).sum_eq_total]
            _ = (1 : MIPStarRE.Quantum.Op ι) := by
                  simp [gHatIdxMeas, completeSubMeas]
            _ =
                gHatHalfProductTotalOperator params family (k + 1) xs *
                  (gHatHalfProductTotalOperator params family (k + 1) xs)ᴴ := by
                  simp [gHatHalfProductTotalOperator_eq_one]
    · simp [gHatHalfProductTotalOperator_eq_one]

/-- Restrict a submeasurement to the outcomes satisfying `p`, dropping all other
mass from the total operator. -/
noncomputable def restrictSubMeas {α : Type*} [Fintype α]
    (A : SubMeas α ι) (p : α → Prop) [DecidablePred p] :
    SubMeas α ι := by
  refine
  { outcome := fun a => if p a then A.outcome a else 0
    total := ∑ a ∈ Finset.univ.filter p, A.outcome a
    outcome_pos := ?_
    sum_eq_total := ?_
    total_le_one := ?_ }
  · intro a
    by_cases ha : p a <;> simp [ha, A.outcome_pos a]
  · simp [Finset.sum_filter]
  · calc
      ∑ a ∈ Finset.univ.filter p, A.outcome a ≤ ∑ a : α, A.outcome a := by
        exact Finset.sum_le_univ_sum_of_nonneg
          (s := Finset.univ.filter p)
          (w := fun a => A.outcome_pos a)
      _ = A.total := A.sum_eq_total
      _ ≤ 1 := A.total_le_one

/-- Restrict the sandwiched completed-slice family to tuples with support of size at
least `d + 1`, matching the `|τ| ≥ d+1` filter in the paper before interpolation. -/
noncomputable def interpolationEligibleSandwichFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas (PointTuple params k) (GHatTupleOutcome params k) ι :=
  fun xs =>
    restrictSubMeas
      (gHatSandwichFamily params family k xs)
      (InterpolationEligible params)

end MIPStarRE.LDT.Pasting
