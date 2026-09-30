import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.Real.Sqrt

/-!
# Section 5 — Combinatorial core of the `r > d` truncation branch

Helper lemmas for the `r > d` branch of `lem:projective-low-rank-sum`
(`references/ldt-paper/orthonormalization.tex:559-658`).

Given a finite family of overlap values `f : α → ℝ` (with `α` the pair index set
`{(a, i)}` carrying `r = |α|` entries) and a chosen `Large ⊂ α` of size
`d < r` such that every `Small = Lᶜ` entry has overlap `≤` every `Large` entry,
the paper derives

* `|Large| * ∑_{Small} f ≤ |Small| * ∑_{Large} f` (pairwise double-counting),
* `r * ∑_{Small} f ≤ |Small| * ∑_{α} f` (partition bound).

We then combine this with the global `R ≤ (1 + 2√ζ) I` estimate to obtain
`∑_{Small} f ≤ 4√ζ` when `ζ ≤ 1/4`, which is the combinatorial heart of the
paper's `4√ζ` truncation error.

These lemmas do **not** depend on the matrix/spectral scaffolding in
`QXPLayer/Core.lean` or `QXPLayer/RankReduction/LowRank.lean`; they are pure
combinatorics over a chosen partition. The per-projector orthonormal range
decomposition is available as `MIPStarRE.Quantum.IsProj.rangeONB`; the concrete
`Large/Small` choice and truncated projectors are assembled in
`QXPLayer/RankReduction/LowRank.lean`.

## References

* `references/ldt-paper/orthonormalization.tex` lines 559–658
  (proof of `lem:projective-low-rank-sum`, `r > d` branch).
-/

open scoped BigOperators

namespace MIPStarRE.LDT.MakingMeasurementsProjective.Truncation

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

end MIPStarRE.LDT.MakingMeasurementsProjective.Truncation
