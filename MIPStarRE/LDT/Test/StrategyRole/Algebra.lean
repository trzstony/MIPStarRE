import MIPStarRE.LDT.Test.StrategyRole.Core

/-!
# Consistency defect of complete measurements

For complete measurements the bipartite consistency defect is one minus the
diagonal matching mass; `qBipartiteConsDefect_of_measurements` records this
identity, which the role-register point-consistency estimates use.
-/

namespace MIPStarRE.LDT

open scoped BigOperators MatrixOrder Matrix ComplexOrder

/-! ### Role-pair projection algebra -/

/-- For complete measurements, the bipartite consistency defect is the total
expectation minus the matching mass. -/
theorem qBipartiteConsDefect_of_measurements {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB))
    (A : Measurement Outcome ιA) (B : Measurement Outcome ιB) :
    qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas =
      ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
        qBipartiteMatchMass ψ A.toSubMeas B.toSubMeas := by
  have hmatch_le :
      qBipartiteMatchMass ψ A.toSubMeas B.toSubMeas ≤
        ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) := by
    calc
      qBipartiteMatchMass ψ A.toSubMeas B.toSubMeas
        = ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a)) := by
            rfl
      _ ≤ ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ιB) (A.outcome a)) := by
            refine Finset.sum_le_sum ?_
            intro a _
            exact ev_mono ψ _ _ <|
              opTensor_le_leftTensor (ι₂ := ιB)
                (A.outcome_pos a) (Measurement.outcome_le_one B a)
      _ = ev ψ (leftTensor (ι₂ := ιB) A.total) := by
            rw [← ev_sum ψ (fun a : Outcome => leftTensor (ι₂ := ιB) (A.outcome a))]
            rw [leftTensor_finset_sum (ι₂ := ιB) Finset.univ A.outcome, A.sum_eq_total]
      _ = ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) := by
            simp [A.total_eq_one, leftTensor]
  unfold qBipartiteConsDefect
  rw [show ev ψ (opTensor A.toSubMeas.total B.toSubMeas.total) =
      ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) by
    simp [A.total_eq_one, B.total_eq_one, opTensor]]
  rw [max_eq_right (sub_nonneg.mpr hmatch_le)]

-- Formal version of the role-register calculation in
-- `references/ldt-paper/inductive_step.tex`, lines 45--66, together with the
-- cross-term-vanishing observation at line 105.  The symmetrized state is
-- supported only on the `A/B` and `B/A` role sectors, while the symmetrized
-- measurements are block diagonal in the standard role basis.
-- Consequently, after taking the normalized trace, an `A/B` sector sees only
-- the left `A` block and right `B` principal block, and the role-reversed sector
-- gives the analogous statement.  These are trace identities, not operator
-- identities: arbitrary off-diagonal role blocks of `Y` need not vanish, but
-- they do not contribute to the paper's expectation calculation.

-- The `Role.A` block of the left tensor only sees the `Role.B` principal block
-- of the right tensor against the classically role-symmetrized state.

-- The `Role.B` block of the left tensor only sees the `Role.A` principal block
-- of the right tensor against the classically role-symmetrized state.

end MIPStarRE.LDT
