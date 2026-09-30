import MIPStarRE.LDT.Commutativity.Scaffold.Core
import MIPStarRE.LDT.MainInductionStep.Defs
import MIPStarRE.LDT.Pasting.Sandwich.PastedFamilies
import MIPStarRE.LDT.Preliminaries.SelfConsistency.Extensions

/-!
# Section 12 pasting: complete and incomplete part self-consistency

Scalar and state-dependent-distance consequences for the complete and incomplete
parts of the pasted slice family.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `lem:q-sdd-complete-part-slice-bound`. -/
lemma qSDD_completePart_le_slice
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (x : Fq params) :
    qSDD ψbi
        ((completePartSubMeas params family x).liftLeft)
        ((completePartSubMeas params family x).liftRight)
      ≤
    qSDD ψbi
        (((family.meas x).toSubMeas).liftLeft)
        (((family.meas x).toSubMeas).liftRight) := by
  let P := family.meas x
  let T : MIPStarRE.Quantum.Op ι := P.total
  have hTT : T * T = T := by
    simpa [T, P] using MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj P
  have hcomplete :
      qSDD ψbi ((completePartSubMeas params family x).liftLeft)
          ((completePartSubMeas params family x).liftRight) =
        ev ψbi (leftTensor (ι₂ := ι) T) +
          ev ψbi (rightTensor (ι₁ := ι) T) -
          2 * ev ψbi (opTensor T T) := by
    calc
      qSDD ψbi ((completePartSubMeas params family x).liftLeft)
          ((completePartSubMeas params family x).liftRight)
        = ev ψbi (((leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T)ᴴ) *
            (leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T)) := by
              unfold qSDD qSDDCore
              simp only [Finset.univ_unique, PUnit.default_eq_unit,
                SubMeas.liftLeft, SubMeas.liftRight,
                mkLeftPlacedSubMeas_outcome, mkRightPlacedSubMeas_outcome,
                Matrix.conjTranspose_sub, Finset.sum_singleton,
                leftTensor_conjTranspose, rightTensor_conjTranspose,
                completePartSubMeas_outcome_unit, completePartSubMeas_total, T]
              simp [P]
      _ = ev ψbi (leftTensor (ι₂ := ι) (T * T)) +
            ev ψbi (rightTensor (ι₁ := ι) (T * T)) - 2 * ev ψbi (opTensor T T) := by
              have hLherm : (leftTensor (ι₂ := ι) T)ᴴ = leftTensor (ι₂ := ι) T := by
                exact
                  (Matrix.nonneg_iff_posSemidef.mp
                    (leftTensor_nonneg (ι₂ := ι)
                      (SubMeas.total_nonneg P.toSubMeas))).isHermitian.eq
              have hRherm : (rightTensor (ι₁ := ι) T)ᴴ = rightTensor (ι₁ := ι) T := by
                exact
                  (Matrix.nonneg_iff_posSemidef.mp
                    (rightTensor_nonneg (ι₁ := ι)
                    (SubMeas.total_nonneg P.toSubMeas))).isHermitian.eq
              calc
                ev ψbi (((leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T)ᴴ) *
                    (leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T))
                  = ev ψbi (((leftTensor (ι₂ := ι) T * leftTensor (ι₂ := ι) T -
                        leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) T) -
                      (rightTensor (ι₁ := ι) T * leftTensor (ι₂ := ι) T -
                        rightTensor (ι₁ := ι) T * rightTensor (ι₁ := ι) T))) := by
                          congr 1
                          simp [hLherm, hRherm, sub_mul, mul_sub]
                          abel
                _ = ev ψbi (leftTensor (ι₂ := ι) (T * T)) +
                      ev ψbi (rightTensor (ι₁ := ι) (T * T)) - 2 * ev ψbi (opTensor T T) := by
                          rw [ev_sub, ev_sub, ev_sub]
                          rw [leftTensor_mul_leftTensor,
                            leftTensor_mul_rightTensor_eq_opTensor,
                            rightTensor_mul_leftTensor_eq_opTensor,
                            rightTensor_mul_rightTensor]
                          ring
      _ = ev ψbi (leftTensor (ι₂ := ι) T) +
            ev ψbi (rightTensor (ι₁ := ι) T) -
            2 * ev ψbi (opTensor T T) := by
            simp [hTT]
  have horig :
      qSDD ψbi (((family.meas x).toSubMeas).liftLeft)
          (((family.meas x).toSubMeas).liftRight) =
        ev ψbi (leftTensor (ι₂ := ι) T) +
          ev ψbi (rightTensor (ι₁ := ι) T) -
          2 * ∑ g : Polynomial params, ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
    have hsum_left :
        ∑ g : Polynomial params, ev ψbi (leftTensor (ι₂ := ι) (P.outcome g)) =
          ev ψbi (leftTensor (ι₂ := ι) T) := by
      calc
        ∑ g : Polynomial params, ev ψbi (leftTensor (ι₂ := ι) (P.outcome g))
          = ev ψbi (∑ a, leftTensor (ι₂ := ι) (P.outcome a)) := by
              rw [← ev_sum ψbi (fun g => leftTensor (ι₂ := ι) (P.outcome g))]
        _ = ev ψbi (leftTensor (ι₂ := ι) (∑ a, P.outcome a)) := by
              rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ P.outcome]
        _ = ev ψbi (leftTensor (ι₂ := ι) T) := by simp [T, P.sum_eq_total]
    have hsum_right :
        ∑ g : Polynomial params, ev ψbi (rightTensor (ι₁ := ι) (P.outcome g)) =
          ev ψbi (rightTensor (ι₁ := ι) T) := by
      calc
        ∑ g : Polynomial params, ev ψbi (rightTensor (ι₁ := ι) (P.outcome g))
          = ev ψbi (∑ a, rightTensor (ι₁ := ι) (P.outcome a)) := by
              rw [← ev_sum ψbi (fun g => rightTensor (ι₁ := ι) (P.outcome g))]
        _ = ev ψbi (rightTensor (ι₁ := ι) (∑ a, P.outcome a)) := by
              rw [← rightTensor_finset_sum (ι₁ := ι) Finset.univ P.outcome]
        _ = ev ψbi (rightTensor (ι₁ := ι) T) := by simp [T, P.sum_eq_total]
    unfold qSDD qSDDCore
    calc
      ∑ g : Polynomial params,
          ev ψbi
            ((((P.toSubMeas.liftLeft).outcome g - (P.toSubMeas.liftRight).outcome g)ᴴ) *
              ((P.toSubMeas.liftLeft).outcome g - (P.toSubMeas.liftRight).outcome g))
        = ∑ g : Polynomial params,
            (ev ψbi (leftTensor (ι₂ := ι) (P.outcome g)) +
              ev ψbi (rightTensor (ι₁ := ι) (P.outcome g)) -
              2 * ev ψbi (opTensor (P.outcome g) (P.outcome g))) := by
              refine Finset.sum_congr rfl ?_
              intro g _
              have hLherm :
                  (leftTensor (ι₂ := ι) (P.outcome g))ᴴ =
                    leftTensor (ι₂ := ι) (P.outcome g) := by
                exact
                  (Matrix.nonneg_iff_posSemidef.mp
                    (leftTensor_nonneg (ι₂ := ι) (P.outcome_pos g))).isHermitian.eq
              have hRherm :
                  (rightTensor (ι₁ := ι) (P.outcome g))ᴴ =
                    rightTensor (ι₁ := ι) (P.outcome g) := by
                exact
                  (Matrix.nonneg_iff_posSemidef.mp
                    (rightTensor_nonneg (ι₁ := ι) (P.outcome_pos g))).isHermitian.eq
              calc
                ev ψbi
                    ((((P.toSubMeas.liftLeft).outcome g - (P.toSubMeas.liftRight).outcome g)ᴴ) *
                      ((P.toSubMeas.liftLeft).outcome g - (P.toSubMeas.liftRight).outcome g))
                  = ev ψbi
                      (((leftTensor (ι₂ := ι) (P.outcome g) *
                            leftTensor (ι₂ := ι) (P.outcome g) -
                          leftTensor (ι₂ := ι) (P.outcome g) *
                            rightTensor (ι₁ := ι) (P.outcome g)) -
                        (rightTensor (ι₁ := ι) (P.outcome g) *
                            leftTensor (ι₂ := ι) (P.outcome g) -
                          rightTensor (ι₁ := ι) (P.outcome g) *
                            rightTensor (ι₁ := ι) (P.outcome g)))) := by
                          congr 1
                          simp [SubMeas.liftLeft, SubMeas.liftRight, hLherm, hRherm,
                            sub_mul, mul_sub]
                          abel
                _ = ev ψbi (leftTensor (ι₂ := ι) (P.outcome g * P.outcome g)) +
                      ev ψbi (rightTensor (ι₁ := ι) (P.outcome g * P.outcome g)) -
                      2 * ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
                          rw [ev_sub, ev_sub, ev_sub]
                          rw [leftTensor_mul_leftTensor,
                            leftTensor_mul_rightTensor_eq_opTensor,
                            rightTensor_mul_leftTensor_eq_opTensor,
                            rightTensor_mul_rightTensor]
                          ring
                _ = ev ψbi (leftTensor (ι₂ := ι) (P.outcome g)) +
                      ev ψbi (rightTensor (ι₁ := ι) (P.outcome g)) -
                      2 * ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
                          simp [P.proj g]
      _ = (∑ g : Polynomial params,
              (ev ψbi (leftTensor (ι₂ := ι) (P.outcome g)) +
                ev ψbi (rightTensor (ι₁ := ι) (P.outcome g)))) -
            ∑ g : Polynomial params, 2 * ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
              rw [Finset.sum_sub_distrib]
      _ = (∑ g : Polynomial params, ev ψbi (leftTensor (ι₂ := ι) (P.outcome g))) +
            ∑ g : Polynomial params, ev ψbi (rightTensor (ι₁ := ι) (P.outcome g)) -
            ∑ g : Polynomial params, 2 * ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
              rw [Finset.sum_add_distrib]
      _ = ev ψbi (leftTensor (ι₂ := ι) T) + ev ψbi (rightTensor (ι₁ := ι) T) -
            ∑ g : Polynomial params, 2 * ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
              rw [hsum_left, hsum_right]
      _ = ev ψbi (leftTensor (ι₂ := ι) T) + ev ψbi (rightTensor (ι₁ := ι) T) -
            2 * ∑ g : Polynomial params, ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
              rw [← Finset.mul_sum]
  have hmatch :
      ∑ g : Polynomial params, ev ψbi (opTensor (P.outcome g) (P.outcome g)) ≤
        ev ψbi (opTensor T T) := by
    simpa [T, P, qMatchMass, leftPlacedSubMeas, rightPlacedSubMeas, postprocess,
      completePartSubMeas, leftTensor_mul_rightTensor_eq_opTensor, P.sum_eq_total] using
      MIPStarRE.LDT.Preliminaries.qMatchMass_leftRight_postprocess_ge
        ψbi P.toSubMeas P.toSubMeas (fun _ => ())
  rw [hcomplete, horig]
  nlinarith

/-- Self-consistency of the incomplete parts `I - G^x`
(`cor:g-bot-self-consistency`).

For projective slices the mirror difference of `I - G^x` is the negative of
that of `G^x`, and the latter is dominated by the slice self-consistency. -/
theorem incompletePart_selfConsistency
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hself : family.StronglySelfConsistent ψbi zeta) :
    SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (incompletePartLeftFamily params family)
      (incompletePartRightFamily params family)
      zeta := by
  rcases hself.sliceSelfConsistency with ⟨hcomplete_bound⟩
  have hcomplete_total :
      sddError ψbi
          (uniformDistribution (SliceQuestion params))
          (completePartLeftFamily params family)
          (completePartRightFamily params family)
        ≤ zeta := by
    unfold sddError at *
    calc
      avgOver (uniformDistribution (SliceQuestion params))
          (fun x =>
            qSDD ψbi
              ((completePartLeftFamily params family) x)
              ((completePartRightFamily params family) x))
        ≤ avgOver (uniformDistribution (SliceQuestion params))
            (fun x =>
              qSDD ψbi
                ((IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas)) x)
                ((IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) x)) := by
              apply avgOver_mono
              intro x
              simpa [completePartLeftFamily, completePartRightFamily,
                IdxSubMeas.liftLeft, IdxSubMeas.liftRight, SubMeas.liftLeft,
                SubMeas.liftRight, leftPlacedSubMeas, rightPlacedSubMeas,
                IdxProjSubMeas.toIdxSubMeas] using
                qSDD_completePart_le_slice params ψbi family x
      _ ≤ zeta := hcomplete_bound
  refine ⟨?_⟩
  calc
    sddError ψbi
        (uniformDistribution (SliceQuestion params))
        (incompletePartLeftFamily params family)
        (incompletePartRightFamily params family)
      =
        sddError ψbi
          (uniformDistribution (SliceQuestion params))
          (completePartLeftFamily params family)
          (completePartRightFamily params family) := by
            unfold sddError
            apply avgOver_congr
            intro x
            unfold qSDD qSDDCore
            let T : MIPStarRE.Quantum.Op ι := (completePartSubMeas params family x).total
            have hdiff :
                leftTensor (ι₂ := ι) (1 - T) - rightTensor (ι₁ := ι) (1 - T) =
                  - (leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T) := by
              ext i j
              rcases i with ⟨i₁, i₂⟩
              rcases j with ⟨j₁, j₂⟩
              simp [T, leftTensor, rightTensor, sub_eq_add_neg]
              ring
            calc
              qSDD ψbi
                  ((incompletePartLeftFamily params family) x)
                  ((incompletePartRightFamily params family) x)
                =
                  ev ψbi
                    (((leftTensor (ι₂ := ι) (1 - T) -
                        rightTensor (ι₁ := ι) (1 - T))ᴴ) *
                      (leftTensor (ι₂ := ι) (1 - T) -
                        rightTensor (ι₁ := ι) (1 - T))) := by
                          simp [qSDD, qSDDCore, incompletePartLeftFamily,
                            incompletePartRightFamily, incompletePartSubMeas,
                            leftPlacedSubMeas, rightPlacedSubMeas, T]
              _ =
                  ev ψbi
                    ((-(leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T))ᴴ *
                      (-(leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T))) := by
                          rw [hdiff]
              _ =
                  ev ψbi
                    (((leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T)ᴴ) *
                      (leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T)) := by
                          have hswap :
                              ((rightTensor (ι₁ := ι) T)ᴴ -
                                  (leftTensor (ι₂ := ι) T)ᴴ) *
                                  (rightTensor (ι₁ := ι) T - leftTensor (ι₂ := ι) T) =
                                ((leftTensor (ι₂ := ι) T)ᴴ -
                                    (rightTensor (ι₁ := ι) T)ᴴ) *
                                  (leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T) := by
                            noncomm_ring
                          simpa [sub_eq_add_neg] using congrArg (ev ψbi) hswap
              _ =
                  qSDD ψbi
                    ((completePartLeftFamily params family) x)
                    ((completePartRightFamily params family) x) := by
                          simp [qSDD, qSDDCore, completePartLeftFamily,
                            completePartRightFamily, completePartSubMeas,
                            leftPlacedSubMeas, rightPlacedSubMeas, T,
                            (family.meas x).sum_eq_total]
    _ ≤ zeta := hcomplete_total

/-- Self-consistency of the completed slice measurements `\widehat G^x`
(`lem:pasting-completion`): the slice outcomes and the incomplete part each
contribute at most `ζ`. -/
theorem gHatSelfConsistency_of_stronglySelfConsistent
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hself : family.StronglySelfConsistent ψbi zeta) :
    SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (2 * zeta) := by
  rcases hself.sliceSelfConsistency with ⟨hcomplete_bound⟩
  rcases incompletePart_selfConsistency params ψbi family zeta hself with
    ⟨hincomplete_bound⟩
  refine ⟨?_⟩
  calc
    sddError ψbi
        (uniformDistribution (SliceQuestion params))
        (gHatSelfConsistencyLeftFamily params family)
        (gHatSelfConsistencyRightFamily params family)
      =
        avgOver (uniformDistribution (SliceQuestion params))
          (fun x =>
            qSDD ψbi
                ((IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas)) x)
                ((IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) x) +
              qSDD ψbi
                ((incompletePartLeftFamily params family) x)
                ((incompletePartRightFamily params family) x)) := by
          unfold sddError
          apply avgOver_congr
          intro x
          unfold qSDD qSDDCore
          rw [Fintype.sum_option]
          simp [gHatSelfConsistencyLeftFamily, gHatSelfConsistencyRightFamily,
            gHatIdxMeas, completeSubMeas, incompletePartLeftFamily,
            incompletePartRightFamily, incompletePartSubMeas, leftPlacedSubMeas,
            rightPlacedSubMeas,
            IdxSubMeas.liftLeft, IdxSubMeas.liftRight, IdxProjSubMeas.toIdxSubMeas,
            add_comm]
    _ =
        sddError ψbi
          (uniformDistribution (SliceQuestion params))
          (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas))
          (IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) +
        sddError ψbi
          (uniformDistribution (SliceQuestion params))
          (incompletePartLeftFamily params family)
          (incompletePartRightFamily params family) := by
            rw [sddError, sddError, avgOver_add]
    _ ≤ zeta + zeta := add_le_add hcomplete_bound hincomplete_bound
    _ = 2 * zeta := by ring

end MIPStarRE.LDT.Pasting
