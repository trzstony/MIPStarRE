import MIPStarRE.LDT.Preliminaries.SelfConsistency.Core
import MIPStarRE.LDT.Test.StrategyFailures

/-!
# Self-consistency after evaluation

`prop:two-notions-of-self-consistency-after-evaluation`: strong
self-consistency of a sub-measurement passes to every post-processing of its
outcomes, in the form of a state-dependent distance bound.

## References

- `blueprint/src/low_degree_simplified.tex`,
  `prop:two-notions-of-self-consistency-after-evaluation`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- `prop:two-notions-of-self-consistency-after-evaluation`.

Proof:
1. Question-dependent postprocessing preserves the total mass and can only
   increase the diagonal overlap term
   `∑_b ⟨ψ|A_[f_q(a)=b] ⊗ A_[f_q(a)=b]|ψ⟩`.
2. Hence bipartite SSC transfers from `A` to the postprocessed family.
3. Apply `twoNotionsOfSelfConsistency` to the postprocessed family. -/
theorem twoNotionsOfSelfConsistencyAfterEvaluation
    {Question α β : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question α ι) (δ : Error) (f : Question → α → β) :
    BipartiteSSCRel ψ 𝒟 A δ →
      SDDRel ψ 𝒟
        (IdxSubMeas.liftLeft (fun q => postprocess (A q) (f q)))
        (IdxSubMeas.liftRight (fun q => postprocess (A q) (f q)))
        (2 * δ) := by
  intro hssc
  have hpost :
      BipartiteSSCRel ψ 𝒟 (fun q => postprocess (A q) (f q)) δ := by
    rcases hssc with ⟨hssc⟩
    constructor
    unfold bipartiteSSCError at *
    calc
      avgOver 𝒟 (fun q => qBipartiteSSCDefect ψ (postprocess (A q) (f q)))
        ≤ avgOver 𝒟 (fun q => qBipartiteSSCDefect ψ (A q)) := by
            apply avgOver_mono
            intro q
            let M := A q
            have hmatch :
                qMatchMass ψ
                    (leftPlacedSubMeas (ιB := ι) (postprocess M (f q)))
                    (rightPlacedSubMeas (ιA := ι) (postprocess M (f q))) ≥
                  qMatchMass ψ
                    (leftPlacedSubMeas (ιB := ι) M)
                    (rightPlacedSubMeas (ιA := ι) M) :=
              qMatchMass_leftRight_postprocess_ge ψ M M (f q)
            have hsub :
                ev ψ (leftTensor (ι₂ := ι) M.total) -
                    qMatchMass ψ
                      (leftPlacedSubMeas (ιB := ι) (postprocess M (f q)))
                      (rightPlacedSubMeas (ιA := ι) (postprocess M (f q)))
                  ≤
                ev ψ (leftTensor (ι₂ := ι) M.total) -
                    qMatchMass ψ
                      (leftPlacedSubMeas (ιB := ι) M)
                      (rightPlacedSubMeas (ιA := ι) M) := by
              linarith
            have hmass_post :
                ev ψ (leftTensor (ι₂ := ι) (postprocess M (f q)).total) =
                  ev ψ (leftTensor (ι₂ := ι) M.total) := by
              simp [postprocess_total]
            have hmatch_post :
                qMatchMass ψ
                    (leftPlacedSubMeas (ιB := ι) (postprocess M (f q)))
                    (rightPlacedSubMeas (ιA := ι) (postprocess M (f q))) =
                  ∑ b : β,
                    ev ψ
                      (opTensor
                        ((postprocess M (f q)).outcome b)
                        ((postprocess M (f q)).outcome b)) := by
              simp [qMatchMass, leftPlacedSubMeas, rightPlacedSubMeas,
                leftTensor_mul_rightTensor_eq_opTensor]
            have hmatch_orig :
                qMatchMass ψ
                    (leftPlacedSubMeas (ιB := ι) M)
                    (rightPlacedSubMeas (ιA := ι) M) =
                  ∑ a : α, ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
              simp [qMatchMass, leftPlacedSubMeas, rightPlacedSubMeas,
                leftTensor_mul_rightTensor_eq_opTensor]
            have hsub' :
                ev ψ (leftTensor (ι₂ := ι) M.total) -
                    ∑ b : β,
                      ev ψ
                        (opTensor
                          ((postprocess M (f q)).outcome b)
                          ((postprocess M (f q)).outcome b))
                  ≤
                ev ψ (leftTensor (ι₂ := ι) M.total) -
                    ∑ a : α, ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
              rw [← hmatch_post, ← hmatch_orig]
              exact hsub
            change
              max 0
                  (ev ψ (leftTensor (ι₂ := ι) (postprocess M (f q)).total) -
                    ∑ b : β,
                      ev ψ
                        (opTensor
                          ((postprocess M (f q)).outcome b)
                          ((postprocess M (f q)).outcome b)))
                ≤
              max 0
                  (ev ψ (leftTensor (ι₂ := ι) M.total) -
                    ∑ a : α, ev ψ (opTensor (M.outcome a) (M.outcome a)))
            rw [hmass_post]
            exact max_le_max le_rfl hsub'
      _ ≤ δ := hssc
  exact twoNotionsOfSelfConsistency ψ 𝒟 (fun q => postprocess (A q) (f q)) δ
    ⟨hperm, hpost⟩

end MIPStarRE.LDT.Preliminaries
