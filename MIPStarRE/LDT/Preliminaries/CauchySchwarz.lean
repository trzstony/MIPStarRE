import MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.InnerProduct

/-!
# Cauchy–Schwarz Inequalities for Approximate Measurements

Formalizes Cauchy–Schwarz-style propositions from Section 3
(Preliminaries) of the LDT paper:
- `closenessOfIP` / `closenessOfIPAdjoint` — Proposition `prop:closeness-of-ip`
  (`eq:closeness3` / `eq:closeness4`)
- `cabApproxDelta` — Proposition `prop:cab-approx-delta`

## References

- `references/ldt-paper/preliminaries.tex`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

lemma sum_ev_mul_le_sqrt
    {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (X Y : Outcome → MIPStarRE.Quantum.Op ι) :
    |∑ a : Outcome, ev ψ (X a * Y a)| ≤
      Real.sqrt (∑ a : Outcome, ev ψ (X a * (X a)ᴴ)) *
        Real.sqrt (∑ a : Outcome, ev ψ ((Y a)ᴴ * Y a)) := by
  calc
    |∑ a : Outcome, ev ψ (X a * Y a)|
      ≤ ∑ a : Outcome, |ev ψ (X a * Y a)| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : Outcome,
          Real.sqrt (ev ψ (X a * (X a)ᴴ)) *
            Real.sqrt (ev ψ ((Y a)ᴴ * Y a)) := by
          refine Finset.sum_le_sum ?_
          intro a ha
          exact ev_abs_mul_le_sqrt ψ (X a) (Y a)
    _ ≤ Real.sqrt
          (∑ a : Outcome, ev ψ (X a * (X a)ᴴ)) *
        Real.sqrt
          (∑ a : Outcome, ev ψ ((Y a)ᴴ * Y a)) := by
          exact
            Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
              (f := fun a => ev ψ (X a * (X a)ᴴ))
              (g := fun a => ev ψ ((Y a)ᴴ * Y a))
              (fun a => by
                simpa using ev_adjoint_self_nonneg ψ ((X a)ᴴ))
              (fun a => ev_adjoint_self_nonneg ψ (Y a))

/-- `prop:closeness-of-ip` (`eq:closeness3`).

If `A ≈_γ B` (raw matrices) and `Σ_a (Σ_b C_{a,b})(Σ_b C_{a,b})† ≤ I`,
then
`|𝔼_x Σ_{a,b} ⟨ψ| C_{a,b} A_a |ψ⟩ -
  𝔼_x Σ_{a,b} ⟨ψ| C_{a,b} B_a |ψ⟩| ≤ √γ`. -/
theorem closenessOfIP
    {Question OutcomeA OutcomeB : Type*} {ι : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : Question → OutcomeA → MIPStarRE.Quantum.Op ι)
    (C : Question → OutcomeA → OutcomeB → MIPStarRE.Quantum.Op ι)
    (γ : Error)
    (hAB : avgOver 𝒟 (fun q => qSDDCore ψ (A q) (B q)) ≤ γ)
    (hC :
      ∀ q,
        ∑ a : OutcomeA,
          (∑ b : OutcomeB, C q a b) * (∑ b : OutcomeB, C q a b)ᴴ ≤ 1) :
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a))| ≤
      Real.sqrt γ := by
  simpa using closenessOfInnerProduct_left ψ hψ 𝒟 h𝒟 A B C γ hAB hC

/-- `prop:closeness-of-ip` (`eq:closeness4`, adjoint version).

If `A† ≈_γ B†` and `Σ_a (Σ_b C_{a,b})†(Σ_b C_{a,b}) ≤ I`, then
`|𝔼_x Σ_{a,b} ⟨ψ| A_a C_{a,b} |ψ⟩ -
  𝔼_x Σ_{a,b} ⟨ψ| B_a C_{a,b} |ψ⟩| ≤ √γ`. -/
theorem closenessOfIPAdjoint
    {Question OutcomeA OutcomeB : Type*} {ι : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : Question → OutcomeA → MIPStarRE.Quantum.Op ι)
    (C : Question → OutcomeA → OutcomeB → MIPStarRE.Quantum.Op ι)
    (γ : Error)
    (hAB :
      avgOver 𝒟
        (fun q => qSDDCore ψ (fun a => (A q a)ᴴ) (fun a => (B q a)ᴴ)) ≤ γ)
    (hC :
      ∀ q,
        ∑ a : OutcomeA,
          (∑ b : OutcomeB, C q a b)ᴴ * (∑ b : OutcomeB, C q a b) ≤ 1) :
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (A q a * C q a b)) -
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (B q a * C q a b))| ≤
      Real.sqrt γ := by
  simpa using closenessOfInnerProduct_right ψ hψ 𝒟 h𝒟 A B C γ hAB hC

/-- `prop:cab-approx-delta`.

If `A ≈_δ B` and `∀ x a, Σ_b (C_{a,b})† C_{a,b} ≤ I`, then
`C_{a,b} A_a ≈_δ C_{a,b} B_a`. -/
theorem cabApproxDelta
    {Question OutcomeA OutcomeB : Type*} {ι : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (𝒟 : Distribution Question)
    (A B : Question → OutcomeA → MIPStarRE.Quantum.Op ι)
    (C : Question → OutcomeA → OutcomeB → MIPStarRE.Quantum.Op ι)
    (δ : Error)
    (hAB : avgOver 𝒟 (fun q => qSDDCore ψ (A q) (B q)) ≤ δ)
    (hC : ∀ q, ∀ a : OutcomeA, ∑ b : OutcomeB, (C q a b)ᴴ * C q a b ≤ 1) :
    avgOver 𝒟
      (fun q =>
        qSDDCore ψ
          (fun ab : OutcomeA × OutcomeB => C q ab.1 ab.2 * A q ab.1)
          (fun ab : OutcomeA × OutcomeB => C q ab.1 ab.2 * B q ab.1))
      ≤ δ := by
  let AOp : IdxOpFamily Question OutcomeA ι := fun q =>
    { outcome := A q
      total := ∑ a : OutcomeA, A q a }
  let BOp : IdxOpFamily Question OutcomeA ι := fun q =>
    { outcome := B q
      total := ∑ a : OutcomeA, B q a }
  have hAB_op : SDDOpRel ψ 𝒟 AOp BOp δ := by
    constructor
    simpa [sddErrorOp, qSDDOp, AOp, BOp] using hAB
  have hcab :
      SDDOpRel ψ 𝒟
        (fun q => ({
          outcome := fun ab : OutcomeA × OutcomeB =>
            C q ab.1 ab.2 * (AOp q).outcome ab.1
          total := ∑ ab : OutcomeA × OutcomeB,
            C q ab.1 ab.2 * (AOp q).outcome ab.1
        } : OpFamily (OutcomeA × OutcomeB) ι))
        (fun q => ({
          outcome := fun ab : OutcomeA × OutcomeB =>
            C q ab.1 ab.2 * (BOp q).outcome ab.1
          total := ∑ ab : OutcomeA × OutcomeB,
            C q ab.1 ab.2 * (BOp q).outcome ab.1
        } : OpFamily (OutcomeA × OutcomeB) ι))
        δ :=
    cabApproxDelta_raw ψ 𝒟 AOp BOp C δ hAB_op hC
  simpa [sddErrorOp, qSDDOp, AOp, BOp] using hcab.squaredDistanceBound

end MIPStarRE.LDT.Preliminaries
