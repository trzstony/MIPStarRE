import MIPStarRE.LDT.Preliminaries.BipartiteSelfConsistency.Completion

/-!
# Self-consistency: core squared-mass bounds

Squared-mass lower bound lemma derived from bipartite self-consistency on
permutation-invariant states (`prop:cool-prop`).

## References

- `references/ldt-paper/preliminaries.tex`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- `prop:other-two-notions-of-self-consistency`.

Proof:
1. Expand `qConsDefect` for the left/right lifts.
2. Bound the total-overlap term `⟨ψ|A ⊗ A|ψ⟩` by `⟨ψ|A ⊗ I|ψ⟩`
   using `A.total ≤ I`.
3. The remaining expression is exactly the bipartite SSC defect.
4. Average over questions and use the hypothesis. -/
theorem otherTwoNotionsOfSelfConsistency {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) (δ : Error) :
    BipartiteSSCRel ψ 𝒟 A δ →
      @ConsRel Question Outcome ι ι _ _ _ _ _ ψ 𝒟 A A δ := by
  intro ⟨hssc⟩
  constructor
  rw [bipartiteConsError_eq_consError_placed]
  unfold consError
  calc
    avgOver 𝒟
        (fun q =>
          qConsDefect ψ ((IdxSubMeas.liftLeft A) q) ((IdxSubMeas.liftRight A) q))
      ≤ avgOver 𝒟 (fun q => qBipartiteSSCDefect ψ (A q)) := by
          apply avgOver_mono
          intro q
          let M := A q
          have htotal_le :
              ev ψ (M.liftLeft.total * M.liftRight.total) ≤
                ev ψ (leftTensor (ι₂ := ι) M.total) := by
            have hopTensor_le :
                opTensor M.total M.total ≤ leftTensor (ι₂ := ι) M.total := by
              have hrewrite :
                  leftTensor (ι₂ := ι) M.total - opTensor M.total M.total =
                    opTensor M.total (1 - M.total) := by
                have hneg :
                    Matrix.kronecker M.total (-M.total) =
                      -Matrix.kronecker M.total M.total := by
                  simpa using
                    (Matrix.kronecker_smul (-1 : ℂ) M.total M.total)
                calc
                  leftTensor (ι₂ := ι) M.total - opTensor M.total M.total
                    = Matrix.kronecker M.total 1 +
                        Matrix.kronecker M.total (-M.total) := by
                          rw [hneg]
                          simp [leftTensor, opTensor, sub_eq_add_neg]
                  _ = Matrix.kronecker M.total (1 - M.total) := by
                        simpa [sub_eq_add_neg] using
                          (Matrix.kronecker_add M.total 1 (-M.total)).symm
                  _ = opTensor M.total (1 - M.total) := by
                        simp [opTensor]
              change
                (leftTensor (ι₂ := ι) M.total - opTensor M.total M.total).PosSemidef
              rw [hrewrite]
              change Matrix.PosSemidef (Matrix.kronecker M.total (1 - M.total))
              exact
                Matrix.PosSemidef.kronecker
                  (Matrix.nonneg_iff_posSemidef.mp M.total_nonneg)
                  (Matrix.nonneg_iff_posSemidef.mp
                    (sub_nonneg.mpr M.total_le_one))
            have hmono :
                ev ψ (opTensor M.total M.total) ≤
                  ev ψ (leftTensor (ι₂ := ι) M.total) :=
              ev_mono ψ _ _ hopTensor_le
            simpa [SubMeas.liftLeft, SubMeas.liftRight,
              leftTensor_mul_rightTensor_eq_opTensor] using hmono
          have hmatch :
              qMatchMass ψ M.liftLeft M.liftRight =
                ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
            simp [qMatchMass, SubMeas.liftLeft, SubMeas.liftRight,
              leftTensor_mul_rightTensor_eq_opTensor]
          have hinner :
              ev ψ (M.liftLeft.total * M.liftRight.total) -
                  qMatchMass ψ M.liftLeft M.liftRight ≤
                ev ψ (leftTensor (ι₂ := ι) M.total) -
                  ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
            rw [hmatch]
            exact sub_le_sub_right htotal_le _
          change
            max 0
                (ev ψ (M.liftLeft.total * M.liftRight.total) -
                  qMatchMass ψ M.liftLeft M.liftRight)
              ≤
            max 0
                (ev ψ (leftTensor (ι₂ := ι) M.total) -
                  ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a)))
          exact max_le_max le_rfl hinner
      _ ≤ δ := hssc

/-- Diagonal consistency for a full measurement is exactly bipartite strong
self-consistency.

This is the converse of `otherTwoNotionsOfSelfConsistency` in the special case
where the indexed family is measurement-valued.  Completeness identifies both
total-mass terms with the identity operator, so the self-`ConsRel` defect
`G ⊗ I ≃ I ⊗ G` and the diagonal SSC defect have the same questionwise
quantity. -/
theorem bipartiteSSCRel_of_consRel_self_measurement {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : IdxMeas Question Outcome ι) (δ : Error) :
    @ConsRel Question Outcome ι ι _ _ _ _ _ ψ 𝒟
        (IdxMeas.toIdxSubMeas A) (IdxMeas.toIdxSubMeas A) δ →
      BipartiteSSCRel ψ 𝒟 (IdxMeas.toIdxSubMeas A) δ := by
  intro ⟨hcons⟩
  constructor
  have hdefect :
      bipartiteSSCError ψ 𝒟 (IdxMeas.toIdxSubMeas A) =
        bipartiteConsError ψ 𝒟
          (IdxMeas.toIdxSubMeas A) (IdxMeas.toIdxSubMeas A) := by
    unfold bipartiteSSCError bipartiteConsError
    apply avgOver_congr
    intro q
    simp [qBipartiteSSCDefect, qBipartiteConsDefect, qBipartiteMatchMass,
      IdxMeas.toIdxSubMeas, (A q).total_eq_one, leftTensor, opTensor]
  simpa [hdefect] using hcons

/-- For full measurements, bipartite SSC and diagonal self-consistency are
equivalent. -/
theorem bipartiteSSCRel_iff_consRel_self_measurement {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : IdxMeas Question Outcome ι) (δ : Error) :
    BipartiteSSCRel ψ 𝒟 (IdxMeas.toIdxSubMeas A) δ ↔
      @ConsRel Question Outcome ι ι _ _ _ _ _ ψ 𝒟
        (IdxMeas.toIdxSubMeas A) (IdxMeas.toIdxSubMeas A) δ := by
  constructor
  · exact otherTwoNotionsOfSelfConsistency ψ 𝒟 (IdxMeas.toIdxSubMeas A) δ
  · exact bipartiteSSCRel_of_consRel_self_measurement ψ 𝒟 A δ

end MIPStarRE.LDT.Preliminaries
