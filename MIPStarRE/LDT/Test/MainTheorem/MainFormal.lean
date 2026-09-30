import MIPStarRE.LDT.Test.MainTheorem.Simplified.SmallError
import MIPStarRE.LDT.Test.MainTheorem.Simplified.Saturated

/-!
# Main-formal soundness theorem

This module contains the final theorem `mainFormal` of the simplified proof
(`thm:main-formal` in `blueprint/src/low_degree_simplified.tex`).  It starts
from a general projective strategy `ProjStrat params ιA ιB` and produces the
three consistency conclusions at the error
`21000 K_{m,d} (ε^(1/64) + (d/q)^(1/64))`, without a sampling parameter.

The sampling-parameter statement of the original paper,
`references/ldt-paper/test_definition.tex:180-202`, is recorded as
`mainFormalWithK` and derived from `mainFormal` by a scalar comparison of the
two error parameters.

## Main results

* `mainFormal`: the simplified quantum soundness theorem.
* `mainFormalWithK`: the original sampling-parameter statement, as a
  corollary of `mainFormal`.

## References

* `blueprint/src/low_degree_simplified.tex`, `thm:main-formal`.
* `references/ldt-paper/test_definition.tex`, `thm:main-formal` at line 180.
-/

namespace MIPStarRE.LDT

namespace Test

/-- Simplified statement of `thm:main-formal`.

The strategy and the three projective-measurement conclusions are those of the
original theorem.  The simplified proof chooses the pasting length internally
and gives the error `21000 K_{m,d} (ε^(1/64) + (d/q)^(1/64))`.

**Local fix:** This bound follows `blueprint/src/low_degree_simplified.tex`,
`thm:main-formal`, which replaces the sampling parameter `k` of
`references/ldt-paper/test_definition.tex:180-202`.  The original statement is
recovered as the corollary `mainFormalWithK`. -/
theorem mainFormal
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.lowIndividualDegreeFailureProbability ≤ eps) :
    ∃ G_A : ProjMeas (Polynomial params) ιA,
      ∃ G_B : ProjMeas (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas)
            (simplifiedMainFormalError params eps) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (simplifiedMainFormalError params eps) ∧
          ConsRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily G_A.toSubMeas)
            (constSubMeasFamily G_B.toSubMeas)
            (simplifiedMainFormalError params eps) := by
  by_cases hlarge : 1 ≤ simplifiedMainFormalError params eps
  · exact mainFormalConclusion_of_one_le params strategy hlarge
  · exact simplifiedMainFormal_smallError params strategy eps ⟨hpass⟩ hlarge

/-- In the nontrivial branch of the sampling-parameter theorem, the simplified
error is at most the original error `mainFormalError`.

If `mainFormalError params k eps < 1`, then `ε` and `d/q` lie in `[0, 1]`,
so their `1/64` powers are at most their `1/40000` powers; moreover
`k ≥ md ≥ d` and `k ≥ 1` give `K_{m,d} ≤ k^2 m^4`. -/
theorem simplifiedMainFormalError_le_mainFormalError
    (params : Parameters) {k : ℕ} {eps : Error}
    (heps : 0 ≤ eps) (hk : params.m * params.d ≤ k) (hk0 : 0 < k)
    (hsmall : ¬ 1 ≤ mainFormalError params k eps) :
    simplifiedMainFormalError params eps ≤ mainFormalError params k eps := by
  set θ : Error := (params.d : Error) / (params.q : Error) with hθdef
  set C : Error := (k : Error) ^ (2 : ℕ) * (params.m : Error) ^ (4 : ℕ) with hCdef
  set E : Error := Real.exp (-((k : Error) / (2560000 * (params.m : Error) ^ (2 : ℕ))))
  set a : Error := Real.rpow eps (1 / (64 : Error))
  set b : Error := Real.rpow θ (1 / (64 : Error))
  set a' : Error := Real.rpow eps (1 / (40000 : Error))
  set b' : Error := Real.rpow θ (1 / (40000 : Error))
  have hθ : 0 ≤ θ := by positivity
  have hk1 : (1 : Error) ≤ k := by exact_mod_cast hk0
  have hm1 : (1 : Error) ≤ params.m := by exact_mod_cast params.hm
  have hC : 1 ≤ C := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hk1) (one_le_pow₀ hm1)
  have ha' : 0 ≤ a' := Real.rpow_nonneg heps _
  have hb' : 0 ≤ b' := Real.rpow_nonneg hθ _
  have hE : 0 ≤ E := Real.exp_nonneg _
  have herr : mainFormalError params k eps = 100000 * C * (a' + b' + E) := by
    simp only [mainFormalError, C, a', b', E, θ]
    ring
  -- The envelope `a' + b' + E` is below one, hence so are `a'` and `b'`.
  have hS : a' + b' + E < 1 := by
    have hlt : 100000 * C * (a' + b' + E) < 1 := herr ▸ lt_of_not_ge hsmall
    nlinarith [mul_nonneg (add_nonneg (add_nonneg ha' hb') hE) (sub_nonneg.mpr hC)]
  have heps1 : eps ≤ 1 := by
    by_contra h
    have : 1 ≤ a' := Real.one_le_rpow (le_of_not_ge h) (by norm_num)
    linarith
  have hθ1 : θ ≤ 1 := by
    by_contra h
    have : 1 ≤ b' := Real.one_le_rpow (le_of_not_ge h) (by norm_num)
    linarith
  have haa' : a ≤ a' := rpow_le_of_denom_le heps heps1 (by norm_num) (by norm_num)
  have hbb' : b ≤ b' := rpow_le_of_denom_le hθ hθ1 (by norm_num) (by norm_num)
  -- The scale `K_{m,d}` is at most `k^2 m^4`.
  have hscale : simplifiedFinalScale params ≤ C := by
    have hm4 : 0 ≤ (params.m : Error) ^ (4 : ℕ) := by positivity
    by_cases hd : params.d = 0
    · simpa [simplifiedFinalScale, hd, C] using
        le_mul_of_one_le_left hm4 (one_le_pow₀ hk1)
    · have hdk : (params.d : Error) ≤ k := by
        exact_mod_cast (Nat.le_mul_of_pos_left params.d params.hm).trans hk
      simpa [simplifiedFinalScale, hd, C] using
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hdk 2) hm4
  have hab : 0 ≤ a + b := add_nonneg (Real.rpow_nonneg heps _) (Real.rpow_nonneg hθ _)
  calc
    simplifiedMainFormalError params eps
        = 21000 * simplifiedFinalScale params * (a + b) := rfl
    _ ≤ 100000 * C * (a + b) :=
        mul_le_mul_of_nonneg_right (by nlinarith [hscale]) hab
    _ ≤ 100000 * C * (a' + b' + E) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = mainFormalError params k eps := herr.symm

/-- Sampling-parameter statement of `thm:main-formal` in the original paper.

Paper origin: `references/ldt-paper/test_definition.tex:180-202`.

This theorem is a corollary of `mainFormal`: in the saturated branch
`mainFormalError params k eps ≥ 1` the conclusion holds for arbitrary
projective polynomial measurements, and otherwise the simplified error is at
most `mainFormalError params k eps`.  The hypothesis `k ≥ m d` is the printed
one.  The additional condition `0 < k` corrects the zero-sampling boundary
where the printed error collapses to zero; this boundary is documented in
`docs/paper-gaps/issue-422-main-formal-zero-k-boundary.tex`. -/
theorem mainFormalWithK
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.lowIndividualDegreeFailureProbability ≤ eps)
    (k : ℕ)
    (hk : params.m * params.d ≤ k)
    (hk0 : 0 < k) :
    ∃ G_A : ProjMeas (Polynomial params) ιA,
      ∃ G_B : ProjMeas (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas)
            (mainFormalError params k eps) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (mainFormalError params k eps) ∧
          ConsRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily G_A.toSubMeas)
            (constSubMeasFamily G_B.toSubMeas)
            (mainFormalError params k eps) := by
  by_cases hlarge : 1 ≤ mainFormalError params k eps
  · exact mainFormalConclusion_of_one_le params strategy hlarge
  · have heps : 0 ≤ eps := ProjStrat.eps_nonneg_of_passes ⟨hpass⟩
    exact MainFormalConclusion.mono (mainFormal params strategy eps hpass)
      (simplifiedMainFormalError_le_mainFormalError params heps hk hk0 hlarge)

end Test

end MIPStarRE.LDT
