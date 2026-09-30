import MIPStarRE.LDT.Preliminaries.Triangles.Core

/-!
# Triangle inequality for consistency

The triangle inequality `prop:simeq-triangle-inequality` for consistency
relations on a bipartite state `ψ ∈ H_A ⊗ H_B`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- Heterogeneous form of `prop:simeq-triangle-inequality`.

This is the paper's triangle step for a general bipartite strategy: the first
and third measurements act on Alice's space, while the second and fourth act on
Bob's space.  No same-space identification or swap symmetry is used. -/
theorem simeqTriangleInequality_heterogeneous
    {Question Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized) (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A C : IdxMeas Question Outcome ιA)
    (B D : IdxMeas Question Outcome ιB)
    (ε δ γ : Error)
    (hAB : ConsRel ψ 𝒟
      (IdxMeas.toIdxSubMeas A)
      (IdxMeas.toIdxSubMeas B) ε)
    (hCB : ConsRel ψ 𝒟
      (IdxMeas.toIdxSubMeas C)
      (IdxMeas.toIdxSubMeas B) δ)
    (hCD : ConsRel ψ 𝒟
      (IdxMeas.toIdxSubMeas C)
      (IdxMeas.toIdxSubMeas D) γ) :
    ConsRel ψ 𝒟
      (IdxMeas.toIdxSubMeas A)
      (IdxMeas.toIdxSubMeas D)
      (ε + 2 * Real.sqrt (δ + γ)) := by
  have hCB_sdd : SDDRel ψ 𝒟
      (IdxSubMeas.placeLeft (ιB := ιB) (IdxMeas.toIdxSubMeas C))
      (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas B))
      (2 * δ) :=
    simeqToApprox_heterogeneous ψ 𝒟 C B δ hCB
  have hCD_sdd : SDDRel ψ 𝒟
      (IdxSubMeas.placeLeft (ιB := ιB) (IdxMeas.toIdxSubMeas C))
      (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas D))
      (2 * γ) :=
    simeqToApprox_heterogeneous ψ 𝒟 C D γ hCD
  have hBC_sdd : SDDRel ψ 𝒟
      (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas B))
      (IdxSubMeas.placeLeft (ιB := ιB) (IdxMeas.toIdxSubMeas C))
      (2 * δ) := by
    exact sddRel_symm ψ 𝒟 _ _ _ hCB_sdd
  have hBD_sdd_raw : SDDRel ψ 𝒟
      (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas B))
      (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas D))
      (2 * ((2 * δ) + (2 * γ))) := by
    exact
      stateDependentDistanceRel_triangle ψ 𝒟
        (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas B))
        (IdxSubMeas.placeLeft (ιB := ιB) (IdxMeas.toIdxSubMeas C))
        (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas D))
        (2 * δ) (2 * γ) hBC_sdd hCD_sdd
  have hBD_sdd : SDDRel ψ 𝒟
      (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas B))
      (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas D))
      (4 * (δ + γ)) := by
    exact
      stateDependentDistanceRel_mono ψ 𝒟
        (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas B))
        (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas D))
        (2 * ((2 * δ) + (2 * γ))) (4 * (δ + γ))
        (by
          ring_nf
          linarith)
        hBD_sdd_raw
  have hδ_nonneg : 0 ≤ δ := by
    rcases hCB with ⟨hδ⟩
    exact le_trans (bipartiteConsError_nonneg ψ 𝒟 _ _) hδ
  have hγ_nonneg : 0 ≤ γ := by
    rcases hCD with ⟨hγ⟩
    exact le_trans (bipartiteConsError_nonneg ψ 𝒟 _ _) hγ
  have hsqrt_four :
      Real.sqrt (4 * (δ + γ)) = 2 * Real.sqrt (δ + γ) := by
    have hδγ_nonneg : 0 ≤ δ + γ := add_nonneg hδ_nonneg hγ_nonneg
    calc
      Real.sqrt (4 * (δ + γ))
        = Real.sqrt (4 : Error) * Real.sqrt (δ + γ) := by
            rw [Real.sqrt_mul (show 0 ≤ (4 : Error) by positivity)]
      _ = 2 * Real.sqrt (δ + γ) := by norm_num
  have hfinal :
      ConsRel ψ 𝒟
        (IdxMeas.toIdxSubMeas A)
        (IdxMeas.toIdxSubMeas D)
        (ε + Real.sqrt (4 * (δ + γ))) := by
    exact
      triangleSub_right_heterogeneous ψ 𝒟 hψ h𝒟
        (IdxMeas.toIdxSubMeas A) B D ε (4 * (δ + γ))
        hAB hBD_sdd
  exact
    (by
      simpa [hsqrt_four] using hfinal)

end MIPStarRE.LDT.Preliminaries
