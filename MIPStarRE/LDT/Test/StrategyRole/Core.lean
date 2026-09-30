import MIPStarRE.LDT.Test.StrategyCore

/-!
# Role-register tensor algebra for the low individual degree test

Role-register operators and strategy symmetrization infrastructure extracted from
`MIPStarRE.LDT.Test.Strategy`.
-/

namespace MIPStarRE.LDT

open scoped BigOperators MatrixOrder Matrix ComplexOrder

/-! ### Role-register tensor algebra -/

/-- Basis projector onto the role sector `r`. -/
def roleProj (r : Role) : MIPStarRE.Quantum.Op Role :=
  Matrix.single r r (1 : ℂ)

/-- The basis projector onto a role sector is positive semidefinite. -/
lemma roleProj_nonneg (r : Role) : 0 ≤ roleProj r := by
  refine Matrix.nonneg_iff_posSemidef.mpr ?_
  let col : Matrix Role Unit ℂ := Matrix.single r () 1
  simpa [roleProj, col] using Matrix.posSemidef_self_mul_conjTranspose col

@[simp] lemma roleProj_mul_self (r : Role) :
    roleProj r * roleProj r = roleProj r := by
  ext i j
  change
    Finset.sum ({Role.A, Role.B} : Finset Role)
      (fun x => roleProj r i x * roleProj r x j) = roleProj r i j
  cases r <;> cases i <;> cases j <;> simp [roleProj]

@[simp] lemma roleProj_A_mul_B :
    roleProj Role.A * roleProj Role.B = 0 := by
  ext i j
  change
    Finset.sum ({Role.A, Role.B} : Finset Role)
      (fun x => roleProj Role.A i x * roleProj Role.B x j) = 0
  cases i <;> cases j <;> simp [roleProj]

@[simp] lemma roleProj_B_mul_A :
    roleProj Role.B * roleProj Role.A = 0 := by
  ext i j
  change
    Finset.sum ({Role.A, Role.B} : Finset Role)
      (fun x => roleProj Role.B i x * roleProj Role.A x j) = 0
  cases i <;> cases j <;> simp [roleProj]

/-- Basis projector onto a pair of role sectors. -/
noncomputable def rolePairProj (rL rR : Role) : MIPStarRE.Quantum.Op (Role × Role) :=
  opTensor (roleProj rL) (roleProj rR)

/-- Distinct role-pair sectors have zero product. -/
theorem rolePairProj_mul_eq_zero_of_ne (rL rR sL sR : Role)
    (h : (rL, rR) ≠ (sL, sR)) :
    rolePairProj rL rR * rolePairProj sL sR = 0 := by
  rw [rolePairProj, rolePairProj, opTensor_mul]
  cases rL <;> cases rR <;> cases sL <;> cases sR <;>
    simp [opTensor] at h ⊢

/-- The projection onto a pair of role sectors is positive semidefinite. -/
lemma rolePairProj_nonneg (rL rR : Role) : 0 ≤ rolePairProj rL rR :=
  opTensor_nonneg (roleProj_nonneg rL) (roleProj_nonneg rR)

@[simp] private lemma swapDensity_leftTensor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Op ι) :
    swapDensity (leftTensor (ι₂ := ι) M) = rightTensor (ι₁ := ι) M := by
  simpa [leftTensor, rightTensor, opTensor, Matrix.kronecker] using
    (swapDensity_opTensor M (1 : MIPStarRE.Quantum.Op ι))

/-- The normalized trace of a two-role sector projection is `1 / 4`. -/
lemma normalizedTrace_rolePairProj (rL rR : Role) :
    MIPStarRE.Quantum.normalizedTrace (rolePairProj rL rR) = (1 / 4 : ℂ) := by
  have hRole : Fintype.card Role = 2 := by decide
  calc
    MIPStarRE.Quantum.normalizedTrace (rolePairProj rL rR)
      = MIPStarRE.Quantum.normalizedTrace (roleProj rL) *
          MIPStarRE.Quantum.normalizedTrace (roleProj rR) :=
            normalizedTrace_opTensor (roleProj rL) (roleProj rR)
    _ = (1 / 2 : ℂ) * (1 / 2 : ℂ) := by
          cases rL <;> cases rR <;>
            simp [MIPStarRE.Quantum.normalizedTrace, roleProj, hRole]
    _ = (1 / 4 : ℂ) := by norm_num

theorem permInvState_of_density_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density) :
    PermInvState ψ := by
  refine ⟨hfix, ?_⟩
  intro M
  unfold ev
  apply congrArg Complex.re
  calc
    MIPStarRE.Quantum.normalizedTrace (ψ.density * leftTensor (ι₂ := ι) M)
      = MIPStarRE.Quantum.normalizedTrace
          (swapDensity (ψ.density * leftTensor (ι₂ := ι) M)) := by
            symm
            exact normalizedTrace_swapDensity _
    _ = MIPStarRE.Quantum.normalizedTrace
          (swapDensity ψ.density * swapDensity (leftTensor (ι₂ := ι) M)) := by
            rw [swapDensity_mul]
    _ = MIPStarRE.Quantum.normalizedTrace (ψ.density * rightTensor (ι₁ := ι) M) := by
            rw [hfix, swapDensity_leftTensor]

end MIPStarRE.LDT
