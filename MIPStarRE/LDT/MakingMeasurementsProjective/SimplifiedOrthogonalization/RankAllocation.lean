import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.Real.Sqrt

/-!
# Global rank allocation for state-dependent orthogonalization

The proof of `lem:state-dependent-orthogonalization` in
`blueprint/src/chapter/low_degree_simplified.tex` selects the largest `d`
weighted eigenvectors across all measurement outcomes.  This file proves the
finite-dimensional linear-programming inequality behind that selection:
a set of `d` indices carrying the largest weights exists, and it dominates
every fractional selection of total mass `d`.

## References

- `blueprint/src/chapter/low_degree_simplified.tex`,
  `lem:state-dependent-orthogonalization`, equation `eq:selected-overlap`.
- `references/ldt-paper/orthonormalization.tex`, Section 5, for the original
  orthogonalization theorem whose conclusion the simplified proof strengthens.
-/

open scoped BigOperators

namespace MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization

/-- Choose `d` elements with the largest values of `f`, breaking ties
arbitrarily. The resulting `Large` set has the paper's ordering property:
every element outside `Large` has value at most every element of `Large`. -/
lemma exists_large_subset_ordered {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) {d : ℕ} (hd : d ≤ Fintype.card α) :
    ∃ L : Finset α, L.card = d ∧
      ∀ s ∈ (Lᶜ : Finset α), ∀ l ∈ L, f s ≤ f l := by
  classical
  let candidates : Finset (Finset α) := (Finset.univ : Finset α).powersetCard d
  have hcandidates : candidates.Nonempty := by
    simpa [candidates] using
      (Finset.powersetCard_nonempty_of_le (s := (Finset.univ : Finset α)) hd)
  obtain ⟨L, hLmem, hLmax⟩ :=
    Finset.exists_max_image candidates (fun T : Finset α => ∑ x ∈ T, f x) hcandidates
  have hL_card : L.card = d := (Finset.mem_powersetCard.mp hLmem).2
  refine ⟨L, hL_card, ?_⟩
  intro s hs l hl
  by_contra hnot
  have hlt : f l < f s := lt_of_not_ge hnot
  have hs_not_mem : s ∉ L := by
    simpa using hs
  let L' : Finset α := insert s (L.erase l)
  have hL'_card : L'.card = d := by
    have hs_erase : s ∉ L.erase l := fun hs' => hs_not_mem (Finset.mem_of_mem_erase hs')
    have hcard_erase : (L.erase l).card = d - 1 := by
      rw [Finset.card_erase_of_mem hl, hL_card]
    have hd_pos : 0 < d := by
      rw [← hL_card]
      exact Finset.card_pos.mpr ⟨l, hl⟩
    calc
      L'.card = (L.erase l).card + 1 := by rw [Finset.card_insert_of_notMem hs_erase]
      _ = d := by omega
  have hL'_mem : L' ∈ candidates := by
    rw [Finset.mem_powersetCard]
    exact ⟨by intro x hx; simp, hL'_card⟩
  have hsum_L' : ∑ x ∈ L', f x = (∑ x ∈ L, f x) - f l + f s := by
    have hs_erase : s ∉ L.erase l := fun hs' => hs_not_mem (Finset.mem_of_mem_erase hs')
    have hsum_erase : ∑ x ∈ L.erase l, f x = (∑ x ∈ L, f x) - f l := by
      have h := Finset.add_sum_erase L f hl
      linarith
    calc
      ∑ x ∈ L', f x = f s + ∑ x ∈ L.erase l, f x := by
        simp [L', hs_erase]
      _ = (∑ x ∈ L, f x) - f l + f s := by
        rw [hsum_erase]
        ring
  have hstrict : (∑ x ∈ L, f x) < ∑ x ∈ L', f x := by
    rw [hsum_L']
    linarith
  exact not_lt_of_ge (hLmax L' hL'_mem) hstrict

/-- A set of the `d` largest weights dominates every fractional selection of
total mass `d`.  This is the global rank-allocation inequality in the simplified
proof, before the weights are specialized to spectral overlap weights
`λ_{a,j} φ(|v_{a,j}⟩⟨v_{a,j}|)`. -/
theorem largest_weights_dominate_fractional {α : Type*}
    [Fintype α]
    (w x : α → ℝ) (d : ℕ)
    (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_le_one : ∀ i, x i ≤ 1)
    (hx_sum : ∑ i, x i = d) :
    ∃ L : Finset α, L.card = d ∧
      ∑ i ∈ L, w i ≥ ∑ i, x i * w i := by
  classical
  have hd : d ≤ Fintype.card α := by
    have hbound : (∑ i, x i) ≤ ∑ _i : α, (1 : ℝ) :=
      Finset.sum_le_sum (fun i _ => hx_le_one i)
    have hsum_one : (∑ _i : α, (1 : ℝ)) = Fintype.card α := by simp
    rw [hx_sum, hsum_one] at hbound
    exact_mod_cast hbound
  obtain ⟨L, hLcard, horder⟩ :=
    exists_large_subset_ordered w hd
  refine ⟨L, hLcard, ?_⟩
  by_cases hLempty : L.Nonempty
  · obtain ⟨threshold, hthreshold_mem, hthreshold_min⟩ :=
      Finset.exists_min_image L w hLempty
    have hselected :
        ∑ i ∈ L, ((1 : ℝ) - x i) * w i ≥
          w threshold * ∑ i ∈ L, ((1 : ℝ) - x i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      simpa [mul_comm] using mul_le_mul_of_nonneg_left
        (hthreshold_min i hi) (sub_nonneg.mpr (hx_le_one i))
    have hunselected :
        ∑ i ∈ (Lᶜ : Finset α), x i * w i ≤
          w threshold * ∑ i ∈ (Lᶜ : Finset α), x i := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      simpa [mul_comm] using mul_le_mul_of_nonneg_left
        (horder i hi threshold hthreshold_mem) (hx_nonneg i)
    have hbalance :
        ∑ i ∈ L, ((1 : ℝ) - x i) =
          ∑ i ∈ (Lᶜ : Finset α), x i := by
      have hpartition := Finset.sum_add_sum_compl (s := L) (f := x)
      have hcard_real : (L.card : ℝ) = (d : ℝ) := by exact_mod_cast hLcard
      calc
        ∑ i ∈ L, ((1 : ℝ) - x i) = (L.card : ℝ) - ∑ i ∈ L, x i := by
          simp [Finset.sum_sub_distrib]
        _ = (d : ℝ) - ∑ i ∈ L, x i := by rw [hcard_real]
        _ = ∑ i ∈ (Lᶜ : Finset α), x i := by linarith [hpartition, hx_sum]
    have hsplit := Finset.sum_add_sum_compl (s := L) (f := fun i => x i * w i)
    have hselected_eq :
        ∑ i ∈ L, ((1 : ℝ) - x i) * w i =
          (∑ i ∈ L, w i) - ∑ i ∈ L, x i * w i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hbalance, hselected_eq] at hselected
    linarith
  · have hL : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hLempty
    have hd_zero : d = 0 := by simpa [hL] using hLcard.symm
    have hx_zero : ∀ i, x i = 0 := by
      intro i
      have hxi_le : x i ≤ ∑ j, x j :=
        Finset.single_le_sum (fun j _ => hx_nonneg j) (Finset.mem_univ i)
      have hsum_zero : (∑ j, x j) = 0 := by simpa [hd_zero] using hx_sum
      linarith only [hxi_le, hx_nonneg i, hsum_zero]
    simp [hL, hx_zero]

/-- The numerical form of `eq:selected-overlap`: when `λ` are measurement
eigenvalues and `r` are state weights, selecting the largest `d` values of
`λᵢ rᵢ` captures at least the quadratic spectral mass `Σᵢ λᵢ² rᵢ`.
The operator-level interpretation is supplied by the spectral projector
construction still required for the full orthogonalization theorem. -/
theorem selected_spectral_overlap {α : Type*} [Fintype α]
    (lam r : α → ℝ) (d : ℕ)
    (hlam_nonneg : ∀ i, 0 ≤ lam i)
    (hlam_le_one : ∀ i, lam i ≤ 1)
    (hlam_sum : ∑ i, lam i = d) :
    ∃ L : Finset α, L.card = d ∧
      ∑ i ∈ L, lam i * r i ≥ ∑ i, (lam i) ^ 2 * r i := by
  obtain ⟨L, hLcard, hbound⟩ :=
    largest_weights_dominate_fractional (fun i => lam i * r i) lam d
      hlam_nonneg hlam_le_one hlam_sum
  refine ⟨L, hLcard, ?_⟩
  simpa [pow_two, mul_assoc] using hbound

end MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization
