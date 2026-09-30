import MIPStarRE.LDT.Basic.DistributionUniform
import MIPStarRE.LDT.Pasting.ComparisonLemmas.Common

/-!
# Line interpolation: averaging and tensor helpers

Tensor/average helper lemmas and total-variation comparison used across the
line interpolation error bounding chain.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma max_zero_add_le
    (a t : Error) (ha : 0 ≤ a) :
    max 0 (a + t) ≤ a + max 0 t := by
  by_cases ht : 0 ≤ t
  · rw [max_eq_right (add_nonneg ha ht), max_eq_right ht]
  · have ht' : t ≤ 0 := le_of_not_ge ht
    by_cases hat : 0 ≤ a + t
    · rw [max_eq_right hat, max_eq_left ht']
      linarith
    · have hat' : a + t ≤ 0 := le_of_not_ge hat
      rw [max_eq_left hat', max_eq_left ht']
      linarith

lemma max_zero_mul_add_le
    (w a t : Error)
    (hw : 0 ≤ w) :
    max 0 (w * a + t) ≤ w * max 0 a + max 0 t := by
  have hwa : w * a ≤ w * max 0 a := by
    exact mul_le_mul_of_nonneg_left (le_max_right 0 a) hw
  calc
    max 0 (w * a + t) ≤ max 0 (w * max 0 a + t) := by
      have hadd : w * a + t ≤ w * max 0 a + t := by linarith
      exact max_le_max le_rfl hadd
    _ ≤ w * max 0 a + max 0 t := by
      exact max_zero_add_le (w * max 0 a) t (mul_nonneg hw (by positivity))

lemma max_zero_avgOver_le_avgOver_max_zero
    {α : Type*}
    (𝒟 : Distribution α)
    (f : α → Error) :
    max 0 (avgOver 𝒟 f) ≤ avgOver 𝒟 (fun a => max 0 (f a)) := by
  classical
  unfold avgOver
  induction 𝒟.support using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      calc
        max 0 (𝒟.weight a * f a + ∑ x ∈ s, 𝒟.weight x * f x)
          ≤ 𝒟.weight a * max 0 (f a) + max 0 (∑ x ∈ s, 𝒟.weight x * f x) := by
              exact max_zero_mul_add_le (𝒟.weight a) (f a)
                (∑ x ∈ s, 𝒟.weight x * f x) (𝒟.nonnegative a)
        _ ≤ 𝒟.weight a * max 0 (f a) + ∑ x ∈ s, 𝒟.weight x * max 0 (f x) := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_right ih (𝒟.weight a * max 0 (f a))

lemma qBipartiteMatchMass_averageIdxSubMeas_left
    {Question Outcome : Type*}
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : SubMeas Outcome ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    qBipartiteMatchMass ψ (averageIdxSubMeas 𝒟 A h𝒟) B =
      avgOver 𝒟 (fun q => qBipartiteMatchMass ψ (A q) B) := by
  classical
  unfold qBipartiteMatchMass averageIdxSubMeas
  calc
    ∑ a,
        ev ψ
          (opTensor (averageOperatorOverDistribution 𝒟 (fun q => (A q).outcome a))
            (B.outcome a))
      = ∑ a, avgOver 𝒟
          (fun q => ev ψ (opTensor ((A q).outcome a) (B.outcome a))) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              exact ev_opTensor_averageOperatorOverDistribution_left ψ 𝒟
                (fun q => (A q).outcome a) (B.outcome a)
    _ = avgOver 𝒟
          (fun q => ∑ a, ev ψ (opTensor ((A q).outcome a) (B.outcome a))) := by
          rw [← avgOver_sum]
    _ = avgOver 𝒟 (fun q => qBipartiteMatchMass ψ (A q) B) := by
          simp [avgOver, qBipartiteMatchMass]

lemma ev_opTensor_total_averageIdxSubMeas_left
    {Question Outcome : Type*}
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : SubMeas Outcome ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    ev ψ (opTensor (averageIdxSubMeas 𝒟 A h𝒟).total B.total) =
      avgOver 𝒟 (fun q => ev ψ (opTensor (A q).total B.total)) := by
  classical
  unfold averageIdxSubMeas
  change ev ψ (opTensor (averageOperatorOverDistribution 𝒟 (fun q => (A q).total)) B.total) = _
  exact ev_opTensor_averageOperatorOverDistribution_left ψ 𝒟 (fun q => (A q).total) B.total

lemma qBipartiteConsDefect_averageIdxSubMeas_left_le
    {Question Outcome : Type*}
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : SubMeas Outcome ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    qBipartiteConsDefect ψ (averageIdxSubMeas 𝒟 A h𝒟) B ≤
      avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (A q) B) := by
  have htotal := ev_opTensor_total_averageIdxSubMeas_left ψ 𝒟 A B h𝒟
  have hmatch := qBipartiteMatchMass_averageIdxSubMeas_left ψ 𝒟 A B h𝒟
  rw [qBipartiteConsDefect, htotal, hmatch]
  rw [← avgOver_sub]
  exact le_trans
    (max_zero_avgOver_le_avgOver_max_zero 𝒟
      (fun q => ev ψ (opTensor (A q).total B.total) - qBipartiteMatchMass ψ (A q) B)) <| by
        refine avgOver_mono 𝒟 _ _ ?_
        intro q
        simp [qBipartiteConsDefect]

end MIPStarRE.LDT.Pasting
