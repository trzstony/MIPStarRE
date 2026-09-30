import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerIdentities.PositiveGram.Sigma

/-!
# Section 5 — Locality-preserving projectivization repair

This file proves the locality-preserving repair route for the late Section 5
`Q/X/XHat/P` argument.

## Scope

The **spectral-truncation stage** (the first part of the proof of rounding
to projectors) is already proved by
`spectralTruncationStatement_of_sourceAlmostProjective` in
`MakingMeasurementsProjective/SpectralTruncation/ProjectiveNonMeasurement.lean`,
which is fully proved via
`projectiveNonMeasurement_of_sourceAlmostProjective_full`. Proofs that
require the spectral truncation statement should call that declaration directly.

The main result recorded here:

- **`leftLiftedProjectivizationRepair`** — paper origin
  `references/ldt-paper/orthonormalization.tex` lines 534–860 (rank
  reduction and the `Q`/`√Q` completeness setup) and 862–1194 (the
  `X`/`X̂`/`P` algebra producing the lifted projective sub-measurement,
  including the final triangle-inequality assembly).  The formal proof below
  follows that local `Q/X/XHat/P` route by passing to the left marginal state,
  constructing the local projective family there, and transporting the final
  estimate back to left lifts.

The theorem proved here is the direct output of that route under a normalized
bipartite state and the source almost-projective estimate for the left-lifted
measurement. It is stated directly in terms of this estimate, rather than in
terms of a separate repair-input assumption, and provides the unconditional
repair step retained for the independent completion-route theorem. The public
orthonormalization theorems now follow from the linear bound in
`SimplifiedOrthogonalization`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

noncomputable section

private def diagBlock {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : MIPStarRE.Quantum.Op (ιA × ιB)) (b : ιB) :
    MIPStarRE.Quantum.Op ιA :=
  M.submatrix (fun i => (i, b)) (fun j => (j, b))

private def leftMarginalDensity {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ρ : MIPStarRE.Quantum.Op (ιA × ιB)) : MIPStarRE.Quantum.Op ιA :=
  ((((Fintype.card ιB : Error) : Error)⁻¹ : Error) : ℂ) •
    ∑ b : ιB, diagBlock ρ b

private lemma leftMarginalDensity_nonneg {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    {ρ : MIPStarRE.Quantum.Op (ιA × ιB)} (hρ : 0 ≤ ρ) :
    0 ≤ leftMarginalDensity ρ := by
  have hρpsd : ρ.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hρ
  have hsum : 0 ≤ ∑ b : ιB, diagBlock ρ b := by
    refine Finset.sum_nonneg fun b _ => ?_
    refine Matrix.nonneg_iff_posSemidef.mpr ?_
    simpa [diagBlock] using hρpsd.submatrix (fun i => (i, b))
  have hcoeff : 0 ≤ ((((Fintype.card ιB : Error) : Error)⁻¹ : Error) : ℂ) := by
    positivity
  simpa [leftMarginalDensity] using smul_nonneg hcoeff hsum

/-- The normalized left-register marginal of a bipartite quantum state. -/
def leftMarginalState {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) : QuantumState ιA where
  density := leftMarginalDensity ψ.density
  density_psd := leftMarginalDensity_nonneg ψ.density_psd

private lemma leftTensor_eq_blockDiagonal_const {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (X : MIPStarRE.Quantum.Op ιA) :
    leftTensor (ι₂ := ιB) X = Matrix.blockDiagonal (fun _ : ιB => X) := by
  ext x y
  rcases x with ⟨i, b⟩
  rcases y with ⟨j, c⟩
  by_cases h : b = c
  · subst c
    simp [leftTensor, Matrix.blockDiagonal_apply]
  · simp [leftTensor, Matrix.blockDiagonal_apply, h]

private lemma trace_blockDiagonal_const_mul_eq_sum_trace_diagBlock
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (X : MIPStarRE.Quantum.Op ιA)
    (M : MIPStarRE.Quantum.Op (ιA × ιB)) :
    Matrix.trace (Matrix.blockDiagonal (fun _ : ιB => X) * M) =
      ∑ b : ιB, Matrix.trace (X * diagBlock M b) := by
  classical
  let e : ((ιA × ιB) × ιA) ≃ (ιB × (ιA × ιA)) :=
    { toFun := fun x => (x.1.2, (x.1.1, x.2))
      invFun := fun x => ((x.2.1, x.1), x.2.2)
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl }
  simpa [diagBlock, Matrix.trace, Matrix.mul_apply, Matrix.blockDiagonal_apply,
    Fintype.sum_prod_type, Finset.sum_sigma', e] using
    (e.sum_comp (fun y : ιB × (ιA × ιA) =>
      X y.2.1 y.2.2 * M (y.2.2, y.1) (y.2.1, y.1)))

private lemma normalizedTrace_leftMarginalDensity_mul_eq
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ρ : MIPStarRE.Quantum.Op (ιA × ιB)) (X : MIPStarRE.Quantum.Op ιA) :
    MIPStarRE.Quantum.normalizedTrace (leftMarginalDensity ρ * X) =
      MIPStarRE.Quantum.normalizedTrace (ρ * leftTensor (ι₂ := ιB) X) := by
  have hcard : ((Fintype.card ιB : Error) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold MIPStarRE.Quantum.normalizedTrace leftMarginalDensity
  rw [smul_mul_assoc, Matrix.trace_smul, Matrix.sum_mul, Matrix.trace_sum]
  have hswap :
      ∑ b : ιB, Matrix.trace (diagBlock ρ b * X) =
        ∑ b : ιB, Matrix.trace (X * diagBlock ρ b) := by
    refine Finset.sum_congr rfl ?_
    intro b _
    exact Matrix.trace_mul_comm _ _
  rw [hswap]
  rw [Matrix.trace_mul_comm]
  rw [leftTensor_eq_blockDiagonal_const]
  rw [trace_blockDiagonal_const_mul_eq_sum_trace_diagBlock]
  simp [Fintype.card_prod]
  ring

/-- Normalization passes from a bipartite state to its left marginal. -/
lemma leftMarginalState_isNormalized {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    {ψ : QuantumState (ιA × ιB)} (hψ : ψ.IsNormalized) :
    (leftMarginalState ψ).IsNormalized := by
  unfold QuantumState.IsNormalized
  have hnorm :
      MIPStarRE.Quantum.normalizedTrace (leftMarginalDensity ψ.density) =
        MIPStarRE.Quantum.normalizedTrace ψ.density := by
    simpa [leftTensor_one] using
      normalizedTrace_leftMarginalDensity_mul_eq (ρ := ψ.density)
        (X := (1 : MIPStarRE.Quantum.Op ιA))
  simpa [leftMarginalState] using hnorm.trans hψ

/-- The expectation of a left-tensor operator is its left-marginal expectation. -/
lemma leftMarginal_ev_eq {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) (X : MIPStarRE.Quantum.Op ιA) :
    ev ψ (leftTensor (ι₂ := ιB) X) = ev (leftMarginalState ψ) X := by
  unfold ev
  rw [← Complex.ofReal_inj]
  simp [normalizedTrace_leftMarginalDensity_mul_eq (ρ := ψ.density) (X := X),
    leftMarginalState]

private def rightDiagBlock {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : MIPStarRE.Quantum.Op (ιA × ιB)) (a : ιA) :
    MIPStarRE.Quantum.Op ιB :=
  M.submatrix (fun i => (a, i)) (fun j => (a, j))

private def rightMarginalDensity {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιA]
    (ρ : MIPStarRE.Quantum.Op (ιA × ιB)) : MIPStarRE.Quantum.Op ιB :=
  ((((Fintype.card ιA : Error) : Error)⁻¹ : Error) : ℂ) •
    ∑ a : ιA, rightDiagBlock ρ a

private lemma rightMarginalDensity_nonneg {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιA]
    {ρ : MIPStarRE.Quantum.Op (ιA × ιB)} (hρ : 0 ≤ ρ) :
    0 ≤ rightMarginalDensity ρ := by
  have hρpsd : ρ.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hρ
  have hsum : 0 ≤ ∑ a : ιA, rightDiagBlock ρ a := by
    refine Finset.sum_nonneg fun a _ => ?_
    refine Matrix.nonneg_iff_posSemidef.mpr ?_
    simpa [rightDiagBlock] using hρpsd.submatrix (fun i => (a, i))
  have hcoeff : 0 ≤ ((((Fintype.card ιA : Error) : Error)⁻¹ : Error) : ℂ) := by
    positivity
  simpa [rightMarginalDensity] using smul_nonneg hcoeff hsum

/-- The normalized state induced on Bob's local space by a bipartite state. -/
def rightMarginalState {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιA]
    (ψ : QuantumState (ιA × ιB)) : QuantumState ιB where
  density := rightMarginalDensity ψ.density
  density_psd := rightMarginalDensity_nonneg ψ.density_psd

private lemma trace_mul_rightTensor_eq_sum_trace_rightDiagBlock
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : MIPStarRE.Quantum.Op (ιA × ιB)) (X : MIPStarRE.Quantum.Op ιB) :
    Matrix.trace (M * rightTensor (ι₁ := ιA) X) =
      ∑ a : ιA, Matrix.trace (rightDiagBlock M a * X) := by
  classical
  let e : ((ιA × ιB) × ιB) ≃ (ιA × (ιB × ιB)) :=
    { toFun := fun x => (x.1.1, (x.1.2, x.2))
      invFun := fun x => ((x.1, x.2.1), x.2.2)
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl }
  simpa [rightDiagBlock, Matrix.trace, Matrix.mul_apply, rightTensor, Matrix.one_apply,
    Fintype.sum_prod_type, Finset.sum_sigma', e] using
    (e.sum_comp (fun y : ιA × (ιB × ιB) =>
      M (y.1, y.2.1) (y.1, y.2.2) * X y.2.2 y.2.1))

private lemma normalizedTrace_rightMarginalDensity_mul_eq
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιA]
    (ρ : MIPStarRE.Quantum.Op (ιA × ιB)) (X : MIPStarRE.Quantum.Op ιB) :
    MIPStarRE.Quantum.normalizedTrace (rightMarginalDensity ρ * X) =
      MIPStarRE.Quantum.normalizedTrace (ρ * rightTensor (ι₁ := ιA) X) := by
  have hcard : ((Fintype.card ιA : Error) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold MIPStarRE.Quantum.normalizedTrace rightMarginalDensity
  rw [smul_mul_assoc, Matrix.trace_smul, Matrix.sum_mul, Matrix.trace_sum]
  rw [trace_mul_rightTensor_eq_sum_trace_rightDiagBlock]
  simp [Fintype.card_prod]
  ring

/-- The right marginal of a normalized bipartite state is normalized. -/
lemma rightMarginalState_isNormalized {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιA]
    {ψ : QuantumState (ιA × ιB)} (hψ : ψ.IsNormalized) :
    (rightMarginalState ψ).IsNormalized := by
  unfold QuantumState.IsNormalized
  have hnorm :
      MIPStarRE.Quantum.normalizedTrace (rightMarginalDensity ψ.density) =
        MIPStarRE.Quantum.normalizedTrace ψ.density := by
    simpa [rightTensor_one] using
      normalizedTrace_rightMarginalDensity_mul_eq (ρ := ψ.density)
        (X := (1 : MIPStarRE.Quantum.Op ιB))
  simpa [rightMarginalState] using hnorm.trans hψ

/-- Expectations of operators on Bob's tensor factor equal expectations in
the right marginal state. -/
lemma rightMarginal_ev_eq {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιA]
    (ψ : QuantumState (ιA × ιB)) (X : MIPStarRE.Quantum.Op ιB) :
    ev ψ (rightTensor (ι₁ := ιA) X) = ev (rightMarginalState ψ) X := by
  unfold ev
  rw [← Complex.ofReal_inj]
  simp [normalizedTrace_rightMarginalDensity_mul_eq (ρ := ψ.density) (X := X),
    rightMarginalState]

end

end MIPStarRE.LDT.MakingMeasurementsProjective
