import MIPStarRE.LDT.MakingMeasurementsProjective.Projectivization

/-!
# Square polar extension

The state-dependent orthogonalization proof uses a unitary polar factor even
when its contraction `X` is singular.  Write `T = √(X†X)`.  Since
`‖Tv‖ = ‖Xv‖` for every vector `v`, the assignment `Tv ↦ Xv` is a well-defined
linear isometry from the range of `T` into the ambient space.  In finite
dimension it extends to an isometry of the whole space, which is the required
unitary `U` with `X = U T`.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of
  `lem:state-dependent-orthogonalization`, the paragraph defining `X` and `U`.
-/

open scoped MatrixOrder Matrix ComplexOrder InnerProductSpace

namespace MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization

/-- Every finite square complex matrix has a unitary polar factor, including
the singular case: `X = U sqrt(X†X)`. -/
theorem exists_unitary_polar_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℂ) :
    ∃ U : Matrix ι ι ℂ,
      U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧ X = U * CFC.sqrt (Xᴴ * X) := by
  classical
  set T : Matrix ι ι ℂ := CFC.sqrt (Xᴴ * X) with hTdef
  have hQ : (0 : Matrix ι ι ℂ) ≤ Xᴴ * X :=
    Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self X)
  have hTT : T * T = Xᴴ * X := CFC.sqrt_mul_sqrt_self _ hQ
  have hTH : Tᴴ = T :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Xᴴ * X))).isHermitian.eq
  set tX := Matrix.toEuclideanLin X with htX
  set tT := Matrix.toEuclideanLin T with htT
  have htT_adj : LinearMap.adjoint tT = tT := by
    rw [htT, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hTH]
  -- `T` and `X` stretch every vector by the same amount.
  have hinner : ∀ v, ⟪tX v, tX v⟫_ℂ = ⟪tT v, tT v⟫_ℂ := by
    intro v
    calc
      ⟪tX v, tX v⟫_ℂ = ⟪LinearMap.adjoint tX (tX v), v⟫_ℂ :=
        (LinearMap.adjoint_inner_left tX v (tX v)).symm
      _ = ⟪tT (tT v), v⟫_ℂ := by
        rw [htX, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, htT,
          ← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, ← LinearMap.comp_apply,
          ← Matrix.toLpLin_mul_same, hTT]
      _ = ⟪tT v, tT v⟫_ℂ := by
        rw [← LinearMap.adjoint_inner_right tT (tT v) v, htT_adj]
  have hnorm : ∀ v, ‖tX v‖ = ‖tT v‖ := by
    intro v
    have h := hinner v
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by exact_mod_cast h)
  have hker : LinearMap.ker tT ≤ LinearMap.ker tX := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have h := hnorm v
    rw [hv, norm_zero] at h
    exact norm_eq_zero.mp h
  -- The isometry `Tv ↦ Xv` on the range of `T`.
  let L₀ : LinearMap.range tT →ₗ[ℂ] EuclideanSpace ℂ ι :=
    (LinearMap.ker tT).liftQ tX hker ∘ₗ (LinearMap.quotKerEquivRange tT).symm.toLinearMap
  have hL₀ : ∀ v, L₀ ⟨tT v, LinearMap.mem_range_self tT v⟩ = tX v := by
    intro v
    simp only [L₀, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  let L : LinearMap.range tT →ₗᵢ[ℂ] EuclideanSpace ℂ ι :=
    { toLinearMap := L₀
      norm_map' := by
        rintro ⟨s, v, rfl⟩
        simpa [hL₀] using hnorm v }
  let U : Matrix ι ι ℂ := Matrix.toEuclideanLin.symm L.extend.toLinearMap
  have hU : Matrix.toEuclideanLin U = L.extend.toLinearMap := by
    simp [U]
  have hUU : Uᴴ * U = 1 := by
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toLpLin_mul_same, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hU,
      Matrix.toLpLin_one]
    refine LinearMap.ext fun x => ext_inner_left ℂ fun y => ?_
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, LinearMap.id_apply]
    exact L.extend.inner_map_map y x
  refine ⟨U, mul_eq_one_comm.mp hUU, hUU, ?_⟩
  apply Matrix.toEuclideanLin.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply, hU, ← htX, ← htT]
  have h := L.extend_apply ⟨tT v, LinearMap.mem_range_self tT v⟩
  simp only [LinearIsometry.coe_toLinearMap] at h ⊢
  rw [h]
  exact (hL₀ v).symm

end MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization
