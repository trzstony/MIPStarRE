import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.Matrix
import MIPStarRE.Quantum.FiniteConicDuality
import MIPStarRE.LDT.SelfImprovement.MatrixRealization.Canonical.StrongDuality.Basic

/-!
# Section 9 -- Canonical SDP separation argument

This module contains the closed-image-cone separation argument and the resulting
zero-duality-gap theorem for the canonical finite-dimensional matrix SDP.

## References

- `references/ldt-paper/self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open Filter
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise Topology

/-- The map sending a primal matrix to its constraint image and objective value. -/
noncomputable def matrixSdpCanonicalPrimalConeMap
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) →L[ℝ]
      MatrixOperator model.space × ℝ :=
  (matrixSdpCanonicalConstraintOperatorCLM params model).prod
    (matrixSdpCanonicalPrimalObjectiveCLM params model)

@[simp]
theorem matrixSdpCanonicalPrimalConeMap_apply
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    matrixSdpCanonicalPrimalConeMap params model X =
      (matrixSdpCanonicalConstraintOperator params model X,
        Complex.re (Matrix.trace (matrixSdpCanonicalObjectiveOperator params model * X))) := by
  simp [matrixSdpCanonicalPrimalConeMap, matrixSdpCanonicalPrimalObjectiveCLM]

/-- The closed image cone of positive semidefinite canonical primal matrices under
the constraint-objective map. -/
noncomputable def matrixSdpCanonicalPrimalImageCone
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    ProperCone ℝ (MatrixOperator model.space × ℝ) :=
  (MIPStarRE.Quantum.opNonnegativeProperCone
      (matrixSdpCanonicalBlockHilbertSpace params model).carrier).map
    (matrixSdpCanonicalPrimalConeMap params model)

/-- An actual positive semidefinite canonical primal matrix maps into the closed
canonical primal image cone. -/
theorem matrixSdpCanonicalPrimalImageCone_mem_of_nonnegative
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : 0 ≤ X) :
    (matrixSdpCanonicalConstraintOperator params model X,
        Complex.re (Matrix.trace (matrixSdpCanonicalObjectiveOperator params model * X))) ∈
      matrixSdpCanonicalPrimalImageCone params model := by
  rw [← matrixSdpCanonicalPrimalConeMap_apply params model X]
  rw [matrixSdpCanonicalPrimalImageCone, ProperCone.mem_map]
  exact subset_closure <| by
    have hXcone :
        X ∈ (MIPStarRE.Quantum.opNonnegativeProperCone
          (matrixSdpCanonicalBlockHilbertSpace params model).carrier).toPointedCone := by
      change 0 ≤ X
      exact hX
    exact (PointedCone.mem_map).2 ⟨X, hXcone, rfl⟩

/-- A feasible canonical primal matrix maps to the image-cone point with
constraint component equal to the identity. -/
theorem matrixSdpCanonicalPrimalImageCone_mem_of_feasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    ((1 : MatrixOperator model.space),
        Complex.re (Matrix.trace (matrixSdpCanonicalObjectiveOperator params model * X))) ∈
      matrixSdpCanonicalPrimalImageCone params model := by
  simpa [hX.constraintEqOne] using
    matrixSdpCanonicalPrimalImageCone_mem_of_nonnegative params model X hX.nonnegative

/-- On the identity constraint fiber, the closed primal image cone contains
exactly the objective values of feasible canonical primal matrices. -/
theorem matrixSdpCanonicalPrimalImageCone_identity_mem_iff_exists_feasible_objective
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) (t : ℝ) :
    ((1 : MatrixOperator model.space), t) ∈
        matrixSdpCanonicalPrimalImageCone params model ↔
      ∃ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
        MatrixSdpCanonicalPrimalFeasible params model X ∧
          Complex.re (Matrix.trace
            (matrixSdpCanonicalObjectiveOperator params model * X)) = t := by
  classical
  constructor
  · intro hmem
    rw [matrixSdpCanonicalPrimalImageCone, ProperCone.mem_map] at hmem
    obtain ⟨u, hu_mem, hu_tendsto⟩ := mem_closure_iff_seq_limit.mp hmem
    have hu_witness : ∀ n : ℕ,
        ∃ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
          X ∈ (MIPStarRE.Quantum.opNonnegativeProperCone
            (matrixSdpCanonicalBlockHilbertSpace params model).carrier).toPointedCone ∧
          (matrixSdpCanonicalPrimalConeMap params model :
            MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) →ₗ[ℝ]
              MatrixOperator model.space × ℝ) X = u n := by
      intro n
      exact PointedCone.mem_map.mp (hu_mem n)
    choose X hXcone hmap using hu_witness
    have hXnonneg : ∀ n : ℕ, 0 ≤ X n := by
      intro n
      have hx := hXcone n
      change 0 ≤ X n at hx
      exact hx
    have hmapCLM : ∀ n : ℕ,
        matrixSdpCanonicalPrimalConeMap params model (X n) = u n := by
      intro n
      simpa using hmap n
    let dimR : ℝ := Fintype.card model.space.carrier
    let R : ℝ := dimR + 1
    let s : Set (MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :=
      {Y | 0 ≤ Y ∧ ‖Y‖ ≤ R}
    have hsBounded : Bornology.IsBounded s := by
      rw [isBounded_iff_forall_norm_le]
      exact ⟨R, fun Y hY => hY.2⟩
    have hcoords :=
      (Prod.tendsto_iff u ((1 : MatrixOperator model.space), t)).mp hu_tendsto
    have htrace_cont : Continuous fun Y : MatrixOperator model.space =>
        Complex.re (Matrix.trace Y) :=
      Complex.continuous_re.comp continuous_id.matrix_trace
    have htrace_tendsto_u :
        Tendsto (fun n : ℕ => Complex.re (Matrix.trace ((u n).1))) atTop
          (𝓝 (Fintype.card model.space.carrier : ℝ)) := by
      change Tendsto (((fun Y : MatrixOperator model.space =>
        Complex.re (Matrix.trace Y)) ∘ fun n : ℕ => (u n).1)) atTop
          (𝓝 (Fintype.card model.space.carrier : ℝ))
      simpa [Matrix.trace_one] using
        (htrace_cont.tendsto (1 : MatrixOperator model.space)).comp hcoords.1
    have htrace_tendsto :
        Tendsto
          (fun n : ℕ => Complex.re (Matrix.trace
            (matrixSdpCanonicalConstraintOperator params model (X n)))) atTop
          (𝓝 dimR) := by
      have htrace_eq :
          (fun n : ℕ => Complex.re (Matrix.trace
            (matrixSdpCanonicalConstraintOperator params model (X n)))) =
            fun n : ℕ => Complex.re (Matrix.trace ((u n).1)) := by
        funext n
        rw [← hmapCLM n]
        rw [matrixSdpCanonicalPrimalConeMap_apply]
      rw [htrace_eq]
      simpa [dimR] using htrace_tendsto_u
    have hdim_lt_R : dimR < R := by
      simp [R]
    have heventTrace : ∀ᶠ n : ℕ in atTop,
        Complex.re (Matrix.trace
          (matrixSdpCanonicalConstraintOperator params model (X n))) < R :=
      htrace_tendsto.eventually (Iio_mem_nhds hdim_lt_R)
    have heventS : ∀ᶠ n : ℕ in atTop, X n ∈ s := by
      filter_upwards [heventTrace] with n hn
      refine ⟨hXnonneg n, ?_⟩
      exact (matrixSdpCanonicalNonnegative_norm_le_constraint_trace_re
        params model (X n) (hXnonneg n)).trans (le_of_lt hn)
    obtain ⟨X₀, _hX₀closure, k, hkmono, hX₀tendsto⟩ :=
      tendsto_subseq_of_frequently_bounded hsBounded heventS.frequently
    have hX₀nonneg : 0 ≤ X₀ :=
      (MIPStarRE.Quantum.isClosed_op_nonnegative
        (ι := (matrixSdpCanonicalBlockHilbertSpace params model).carrier)).mem_of_tendsto
        hX₀tendsto (Eventually.of_forall fun n => hXnonneg (k n))
    have hmap_tendsto_X₀ :
        Tendsto
          (fun n : ℕ => matrixSdpCanonicalPrimalConeMap params model (X (k n)))
          atTop (𝓝 (matrixSdpCanonicalPrimalConeMap params model X₀)) :=
      ((matrixSdpCanonicalPrimalConeMap params model).continuous.tendsto X₀).comp
        hX₀tendsto
    have hu_subseq_tendsto :
        Tendsto (u ∘ k) atTop (𝓝 ((1 : MatrixOperator model.space), t)) :=
      hu_tendsto.comp hkmono.tendsto_atTop
    have hmap_tendsto_identity :
        Tendsto
          (fun n : ℕ => matrixSdpCanonicalPrimalConeMap params model (X (k n)))
          atTop (𝓝 ((1 : MatrixOperator model.space), t)) := by
      have hfun :
          (fun n : ℕ => matrixSdpCanonicalPrimalConeMap params model (X (k n))) =
            u ∘ k := by
        funext n
        exact hmapCLM (k n)
      rw [hfun]
      exact hu_subseq_tendsto
    have hlimit :
        matrixSdpCanonicalPrimalConeMap params model X₀ =
          ((1 : MatrixOperator model.space), t) :=
      tendsto_nhds_unique hmap_tendsto_X₀ hmap_tendsto_identity
    have hconstraint :
        matrixSdpCanonicalConstraintOperator params model X₀ =
          (1 : MatrixOperator model.space) := by
      have := congrArg Prod.fst hlimit
      simpa [matrixSdpCanonicalPrimalConeMap_apply] using this
    have hobjective :
        Complex.re (Matrix.trace
            (matrixSdpCanonicalObjectiveOperator params model * X₀)) = t := by
      have := congrArg Prod.snd hlimit
      simpa [matrixSdpCanonicalPrimalConeMap_apply] using this
    exact ⟨X₀, ⟨hX₀nonneg, hconstraint⟩, hobjective⟩
  · rintro ⟨X, hX, hobj⟩
    simpa [hobj] using matrixSdpCanonicalPrimalImageCone_mem_of_feasible params model X hX

/-- A feasible functional dual bound on the canonical primal image cone gives a
paper-form dual feasible matrix through the Hermitian trace-pairing
representation. -/
theorem matrixSdpCanonicalTracePairingDualMatrix_dualFeasible_of_conicFunctionalDualFeasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (ψ : StrongDual ℝ (MatrixOperator model.space))
    (hψ : ∀ z ∈ matrixSdpCanonicalPrimalImageCone params model, z.2 ≤ ψ z.1) :
    ∀ g : Polynomial params,
      0 ≤ matrixSdpDualSlackOperator params model
        (MIPStarRE.Quantum.hermitianTracePairingMatrixOfRealCLM ψ) g := by
  let W := MIPStarRE.Quantum.hermitianTracePairingMatrixOfRealCLM ψ
  refine matrixSdpCanonicalDualConstraint_nonneg_of_trace_pairing_nonneg
    params model W ?_ ?_
  · exact matrixSdpCanonicalDualOperator_sub_objectiveOperator_isHermitian
      params model W (MIPStarRE.Quantum.hermitianTracePairingMatrixOfRealCLM_isHermitian ψ)
  · intro X hX
    have hle :
        Complex.re (Matrix.trace
            (matrixSdpCanonicalObjectiveOperator params model * X)) ≤
          Complex.re (Matrix.trace
            (matrixSdpCanonicalDualOperator params model W * X)) := by
      have hmem :=
        matrixSdpCanonicalPrimalImageCone_mem_of_nonnegative params model X hX
      have hfunctional := hψ
        (matrixSdpCanonicalConstraintOperator params model X,
          Complex.re (Matrix.trace
            (matrixSdpCanonicalObjectiveOperator params model * X))) hmem
      have hconstraintHerm :
          (matrixSdpCanonicalConstraintOperator params model X).IsHermitian :=
        matrixSdpCanonicalConstraintOperator_isHermitian_of_nonnegative params model hX
      rw [MIPStarRE.Quantum.hermitianTracePairingMatrixOfRealCLM_apply_of_isHermitian
        ψ hconstraintHerm] at hfunctional
      rwa [← matrixSdpCanonicalDualOperator_trace_constraint params model X W]
        at hfunctional
    rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
    exact sub_nonneg.mpr hle

/-- A paper-form dual minimizer is also minimal among feasible functional dual
bounds on the canonical primal image cone. -/
theorem matrixSdpCanonicalFunctionalDualObjective_min_of_matrixDualMin
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (hZmin : ∀ W : MatrixOperator model.space,
      (∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model W g) →
      matrixSdpDualObjective model Z ≤ matrixSdpDualObjective model W) :
    ∀ ψ : StrongDual ℝ (MatrixOperator model.space),
      (∀ z ∈ matrixSdpCanonicalPrimalImageCone params model, z.2 ≤ ψ z.1) →
      matrixSdpDualObjective model Z ≤ ψ (1 : MatrixOperator model.space) := by
  intro ψ hψ
  let W := MIPStarRE.Quantum.hermitianTracePairingMatrixOfRealCLM ψ
  have hWdual :
      ∀ g : Polynomial params, 0 ≤ matrixSdpDualSlackOperator params model W g := by
    simpa [W] using
      matrixSdpCanonicalTracePairingDualMatrix_dualFeasible_of_conicFunctionalDualFeasible
        params model ψ hψ
  have hd_le_W := hZmin W hWdual
  have hI : (1 : MatrixOperator model.space).IsHermitian := Matrix.isHermitian_one
  have hWobj : matrixSdpDualObjective model W = ψ (1 : MatrixOperator model.space) := by
    have hψI :=
      MIPStarRE.Quantum.hermitianTracePairingMatrixOfRealCLM_apply_of_isHermitian ψ hI
    simpa [matrixSdpDualObjective, W] using hψI.symm
  simpa [hWobj] using hd_le_W

/-- The canonical primal objective attains a maximum on the feasible set. -/
theorem matrixSdpCanonicalPrimalObjective_exists_isMaxOn
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    ∃ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
      MatrixSdpCanonicalPrimalFeasible params model X ∧
        ∀ Y : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
          MatrixSdpCanonicalPrimalFeasible params model Y →
            Complex.re (Matrix.trace (matrixSdpCanonicalObjectiveOperator params model * Y)) ≤
              Complex.re (Matrix.trace (matrixSdpCanonicalObjectiveOperator params model * X)) := by
  obtain ⟨X, hX, hmax⟩ :=
    (matrixSdpCanonicalPrimalFeasible_isCompact params model).exists_isMaxOn
      (Set.nonempty_def.mpr (matrixSdpCanonicalPrimalFeasible_nonempty params model))
      (continuous_matrixSdpCanonicalPrimalObjective params model).continuousOn
  exact ⟨X, hX, fun Y hY => hmax hY⟩

/-- The canonical primal maximizer and dual minimizer exist, and their attained
values satisfy weak duality. This packages the attained optima but is not the
zero-gap strong-duality theorem. -/
theorem matrixSdpCanonicalPrimalDualOptima_exist
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    ∃ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
      ∃ Z : MatrixOperator model.space,
        MatrixSdpCanonicalPrimalFeasible params model X ∧
        (∀ g : Polynomial params,
          0 ≤ matrixSdpDualSlackOperator params model Z g) ∧
        (∀ Y : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
          MatrixSdpCanonicalPrimalFeasible params model Y →
            Complex.re (Matrix.trace
              (matrixSdpCanonicalObjectiveOperator params model * Y)) ≤
              Complex.re (Matrix.trace
                (matrixSdpCanonicalObjectiveOperator params model * X))) ∧
        (∀ W : MatrixOperator model.space,
          (∀ g : Polynomial params,
            0 ≤ matrixSdpDualSlackOperator params model W g) →
          matrixSdpDualObjective model Z ≤ matrixSdpDualObjective model W) ∧
        Complex.re (Matrix.trace
          (matrixSdpCanonicalObjectiveOperator params model * X)) ≤
          matrixSdpDualObjective model Z := by
  obtain ⟨X, hX, hXmax⟩ :=
    matrixSdpCanonicalPrimalObjective_exists_isMaxOn params model
  obtain ⟨Z, hZ, hZmin⟩ :=
    matrixSdpCanonicalDualObjective_exists_isMinOn params model
  refine ⟨X, Z, hX, hZ, hXmax, hZmin, ?_⟩
  exact matrixSdpCanonicalWeakDuality params model X hX Z
    (matrixSdpCanonicalDualConstraint_nonneg_of_dualFeasible params model Z hZ)

/-- The canonical matrix SDP has a primal-dual optimal pair with zero duality
gap.

This is the finite-dimensional strong-duality conclusion used in the paper's
Section 9 SDP argument.  The proof combines compact attainment, separation of
the closed primal image cone, and the trace-pairing representation of the
normalized separator; it does not add an auxiliary dominance hypothesis on the
dual matrix. -/
theorem matrixSdpCanonicalStrongDuality
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    ∃ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
      ∃ Z : MatrixOperator model.space,
        MatrixSdpCanonicalPrimalFeasible params model X ∧
        (∀ g : Polynomial params,
          0 ≤ matrixSdpDualSlackOperator params model Z g) ∧
        Complex.re (Matrix.trace
            (matrixSdpCanonicalObjectiveOperator params model * X)) =
          matrixSdpDualObjective model Z := by
  obtain ⟨X, Z, hX, hZ, hXmax, hZmin, hweak⟩ :=
    matrixSdpCanonicalPrimalDualOptima_exist params model
  let p : ℝ := Complex.re (Matrix.trace
    (matrixSdpCanonicalObjectiveOperator params model * X))
  let d : ℝ := matrixSdpDualObjective model Z
  have hp_eq_d : p = d := by
    refine MIPStarRE.Quantum.conic_primalValue_eq_dualValue_of_fiber_max_dual_min
      (C := matrixSdpCanonicalPrimalImageCone params model)
      (y := (1 : MatrixOperator model.space)) (p := p) (d := d) ?_ ?_ ?_ ?_
    · simpa [p] using matrixSdpCanonicalPrimalImageCone_mem_of_feasible params model X hX
    · intro t hmem
      obtain ⟨Y, hY, hYobj⟩ :=
        (matrixSdpCanonicalPrimalImageCone_identity_mem_iff_exists_feasible_objective
          params model t).mp hmem
      have ht_le : t ≤ p := by
        simpa [p, hYobj] using hXmax Y hY
      exact ht_le
    · intro ψ hψ
      simpa [d] using
        matrixSdpCanonicalFunctionalDualObjective_min_of_matrixDualMin
          params model Z hZmin ψ hψ
    · simpa [p, d] using hweak
  refine ⟨X, Z, hX, hZ, ?_⟩
  simpa [p, d] using hp_eq_d

end MIPStarRE.LDT.SelfImprovement
