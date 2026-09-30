import MIPStarRE.LDT.Preliminaries.BipartiteSelfConsistency.Completion

/-!
# Preliminary comparison theorems: chain rules

Monotonicity and chain rules for the state-dependent distance of operator
families, the multi-step form of `prop:triangle-inequality-for-approx_delta`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- Questionwise n-step chain bound: the squared distance between the
first and last operator family telescopes and is bounded by
`n * ∑ individual squared distances` via `ev_sum_conjTranspose_mul_sum_le`. -/
private lemma questionSDDOp_chain
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (n : ℕ)
    (families : Fin (n + 1) → OpFamily Outcome ι) :
    qSDDOp ψ (families 0) (families (Fin.last n)) ≤
      (n : ℝ) * ∑ i : Fin n,
        qSDDOp ψ (families i.castSucc) (families i.succ) := by
  -- Define the per-step difference operators
  let D : Fin n → Outcome → MIPStarRE.Quantum.Op ι := fun i a =>
    (families i.castSucc).outcome a - (families i.succ).outcome a
  -- Telescoping: total difference = sum of step differences
  have htelescope : ∀ a,
      (families 0).outcome a - (families (Fin.last n)).outcome a =
        ∑ i : Fin n, D i a := by
    intro a
    change (families 0).outcome a -
        (families (Fin.last n)).outcome a =
      ∑ i : Fin n, ((families i.castSucc).outcome a -
        (families i.succ).outcome a)
    rw [Finset.sum_sub_distrib, sub_eq_sub_iff_add_eq_add]
    exact (Fin.sum_univ_succ
      (fun j => (families j).outcome a)).symm.trans
      (Fin.sum_univ_castSucc
        (fun j => (families j).outcome a))
  unfold qSDDOp qSDDCore
  calc ∑ a : Outcome,
        ev ψ (((families 0).outcome a -
            (families (Fin.last n)).outcome a)ᴴ *
          ((families 0).outcome a -
            (families (Fin.last n)).outcome a))
      = ∑ a, ev ψ ((∑ i : Fin n, D i a)ᴴ *
          (∑ i : Fin n, D i a)) := by
        exact Finset.sum_congr rfl fun a _ => by
          rw [htelescope a]
    _ ≤ ∑ a, ((n : ℝ) * ∑ i : Fin n,
          ev ψ ((D i a)ᴴ * D i a)) := by
        refine Finset.sum_le_sum fun a _ => ?_
        have := ev_sum_conjTranspose_mul_sum_le ψ
          (fun i => D i a)
        rwa [Fintype.card_fin] at this
    _ = (n : ℝ) * ∑ i : Fin n, ∑ a,
          ev ψ ((D i a)ᴴ * D i a) := by
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_comm

/-- n-step SDDOpRel chain lemma via vector Cauchy-Schwarz.

Given `n` consecutive SDDOpRel bounds, the endpoints satisfy an SDDOpRel
bound with error `n * (∑ individual errors)`.  This improves on naive
triangle-inequality chaining, which would give exponential blowup.

Paper reference: `prop:triangle-inequality-for-approx_delta` in
`references/ldt-paper/preliminaries.tex`.

Proof sketch: telescoping + `‖∑ dᵢ|ψ⟩‖² ≤ n · ∑ ‖dᵢ|ψ⟩‖²`
(vector Cauchy-Schwarz / norm triangle inequality). -/
lemma sddOpRel_chain
    {Question Outcome : Type*} {ι' : Type*}
    [Fintype ι'] [DecidableEq ι'] [Fintype Outcome]
    (ψ : QuantumState ι') (𝒟 : Distribution Question)
    (n : ℕ)
    (families : Fin (n + 1) → IdxOpFamily Question Outcome ι')
    (errors : Fin n → Error)
    (hsteps : ∀ i : Fin n,
      SDDOpRel ψ 𝒟 (families i.castSucc) (families i.succ)
        (errors i)) :
    SDDOpRel ψ 𝒟 (families 0) (families (Fin.last n))
      ((n : Error) * ∑ i : Fin n, errors i) := by
  constructor
  unfold sddErrorOp at *
  -- Lift the questionwise chain bound through avgOver
  calc avgOver 𝒟 (fun q =>
        qSDDOp ψ (families 0 q) (families (Fin.last n) q))
      ≤ avgOver 𝒟 (fun q => (n : ℝ) * ∑ i : Fin n,
          qSDDOp ψ (families i.castSucc q)
            (families i.succ q)) := by
        exact avgOver_mono 𝒟 _ _ fun q =>
          questionSDDOp_chain ψ n (fun j => families j q)
    _ = (n : ℝ) * avgOver 𝒟 (fun q => ∑ i : Fin n,
          qSDDOp ψ (families i.castSucc q)
            (families i.succ q)) := by
        rw [avgOver_const_mul]
    _ = (n : ℝ) * ∑ i : Fin n, avgOver 𝒟 (fun q =>
          qSDDOp ψ (families i.castSucc q)
            (families i.succ q)) := by
        congr 1
        simp only [avgOver, Finset.mul_sum]
        exact Finset.sum_comm
    _ ≤ (n : ℝ) * ∑ i : Fin n, errors i := by
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun i _ =>
            (hsteps i).squaredDistanceBound)
          (Nat.cast_nonneg n)

end MIPStarRE.LDT.Preliminaries
