import MIPStarRE.LDT.MainInductionStep.Simplified.Statements
import MIPStarRE.LDT.MainInductionStep.Theorems.PastingAssembly.Basic

/-!
# Averaged errors in the simplified induction

The restricted-probabilities lemma bounds the mean slice test errors.
Concavity of fractional powers converts those bounds into the mean
recursive and dilation errors used in the successor step.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-induction`.
- `references/ldt-paper/inductive_step.tex:374-412`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open MIPStarRE.LDT.SelfImprovement
open scoped BigOperators

/-- Jensen's inequality followed by the conditioning-loss estimate for a
fractional power. -/
theorem average_fractional_power_le_loss
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (f : α → Error) (n : ℕ) (hn : 1 ≤ n)
    (x c : Error)
    (hf : ∀ a, 0 ≤ f a)
    (hx : 0 ≤ x) (hc : 1 ≤ c)
    (havg : avgOver (uniformDistribution α) f ≤ c * x) :
    avgOver (uniformDistribution α)
        (fun a => Real.rpow (f a) (1 / (n : Error))) ≤
      c * Real.rpow x (1 / (n : Error)) := by
  have hnreal : (1 : Error) ≤ (n : Error) := by exact_mod_cast hn
  have hp0 : 0 ≤ (1 / (n : Error)) := by positivity
  have hp1 : (1 / (n : Error)) ≤ 1 := by
    exact (div_le_iff₀ (by positivity : (0 : Error) < n)).2 (by linarith)
  have hcx : 0 ≤ c * x := mul_nonneg (by linarith) hx
  have hcPow : Real.rpow c (1 / (n : Error)) ≤ c := by
    simpa using Real.rpow_le_rpow_of_exponent_le hc hp1
  calc
    avgOver (uniformDistribution α)
        (fun a => Real.rpow (f a) (1 / (n : Error))) ≤
        Real.rpow (avgOver (uniformDistribution α) f)
          (1 / (n : Error)) :=
      avgOver_uniform_rpow_one_div_le_rpow_avg f n hn hf
    _ ≤ Real.rpow (c * x) (1 / (n : Error)) := by
      exact Real.rpow_le_rpow
        (avgOver_nonneg (uniformDistribution α) f hf) havg hp0
    _ = Real.rpow c (1 / (n : Error)) *
        Real.rpow x (1 / (n : Error)) :=
      Real.mul_rpow (by linarith) hx
    _ ≤ c * Real.rpow x (1 / (n : Error)) := by
      exact mul_le_mul_of_nonneg_right hcPow (Real.rpow_nonneg hx _)

/-- The four fractional-power terms in the positive-degree induction error. -/
noncomputable def simplifiedPositiveErrorSum
    (params : Parameters) (eps delta gamma : Error) : Error :=
  Real.rpow eps (1 / (32 : Error)) +
    Real.rpow delta (1 / (32 : Error)) +
    Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (32 : Error)) +
    Real.rpow gamma (1 / (8 : Error))

/-- The slice conditioning factor `(m+1)/m` is at least one. -/
theorem one_le_sliceConditioningLoss (params : Parameters) :
    (1 : Error) ≤ sliceConditioningLoss params := by
  unfold sliceConditioningLoss
  have hm : (0 : Error) < (params.m : Error) := by
    exact_mod_cast params.hm
  apply (one_le_div₀ hm).2
  exact_mod_cast Nat.le_succ params.m

end MIPStarRE.LDT.MainInductionStep
