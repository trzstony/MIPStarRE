import MIPStarRE.LDT.SelfImprovement.Theorems.Results.BoundednessTransport.PointConsistency

/-!
# Boundedness transport boundedness-gap estimates

This file contains the helper boundedness-gap decomposition, its
data-processing transport, and the final projective-residual boundedness
constructors used in the self-improvement proof.

## References

- `references/ldt-paper/self_improvement.tex` lines 612--613 and 742--755
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.Quantum
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Algebraic decomposition of the helper boundedness gap.

The scalar gap
`⟨Z ⊗ I - helperAgreementAverageOperator⟩` is the sum of
`⟨Z ⊗ I⟩ - ⟨I ⊗ H.total⟩` and the off-diagonal average produced by
`helper_boundedness_slack_average_ev_eq_off_diagonal_avg`.  This is the
formal algebraic bridge between the reindexing calculation and the final
boundedness estimate in the proof of self-improvement. -/
theorem helper_boundedness_gap_eq_upper_gap_add_off_diagonal_avg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) :
    helperBoundednessGap params strategy H Z =
      (ev strategy.state (helperUpperOperator params Z) -
          ev strategy.state (rightTensor (ι₁ := ι) H.total)) +
        avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ h : Polynomial params,
            ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
              ev strategy.state
                (opTensor ((strategy.pointMeasurement u).outcome a)
                  (H.outcome h))) := by
  have hslack :=
    helper_boundedness_slack_average_ev_eq_off_diagonal_avg params strategy H
  have hgap_decomp :
      helperBoundednessGap params strategy H Z =
        (ev strategy.state (helperUpperOperator params Z) -
            ev strategy.state (rightTensor (ι₁ := ι) H.total)) +
          (ev strategy.state (rightTensor (ι₁ := ι) H.total) -
            ev strategy.state (helperAgreementAverageOperator params strategy H)) := by
    unfold helperBoundednessGap helperBoundednessOperator
    rw [ev_sub]
    ring
  rw [hgap_decomp, hslack]

/-- Helper-stage boundedness from the scalar comparison and the off-diagonal
estimate.

The helper boundedness gap decomposes as
`⟨Z ⊗ I⟩ - ⟨I ⊗ Hhat.total⟩` plus the off-diagonal average from
`helper_boundedness_slack_average_ev_eq_off_diagonal_avg`.  Thus the comparison
`⟨Z ⊗ I⟩ - ⟨I ⊗ Hhat.total⟩ ≤ 3 √δ`, together with the off-diagonal estimate
`≤ 4 √ζ_variance`, gives the helper threshold after applying
`helper_boundedness_error_le_selfImprovementHelperError`. -/
theorem helper_boundedness_gap_le_selfImprovementHelperError
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hZ_vs_H :
      ev strategy.state (helperUpperOperator params Z) -
          ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) ≤
        3 * Real.sqrt delta)
    (hoffdiag :
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (Hhat.outcome h))) ≤
        4 * Real.sqrt (selfImprovementVarianceError params eps delta)) :
    helperBoundednessGap params strategy Hhat Z ≤
      selfImprovementHelperError params eps delta := by
  calc
    helperBoundednessGap params strategy Hhat Z =
        (ev strategy.state (helperUpperOperator params Z) -
            ev strategy.state (rightTensor (ι₁ := ι) Hhat.total)) +
          avgOver (uniformDistribution (Point params)) (fun u =>
            ∑ h : Polynomial params,
              ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
                ev strategy.state
                  (opTensor ((strategy.pointMeasurement u).outcome a)
                    (Hhat.outcome h))) :=
      helper_boundedness_gap_eq_upper_gap_add_off_diagonal_avg params strategy Hhat Z
    _ ≤ 3 * Real.sqrt delta +
        4 * Real.sqrt (selfImprovementVarianceError params eps delta) :=
      add_le_add hZ_vs_H hoffdiag
    _ ≤ selfImprovementHelperError params eps delta :=
      helper_boundedness_error_le_selfImprovementHelperError params eps delta heps hdelta

-- This bound combines the off-diagonal add-in-u transfer with the boundedness
-- gap decomposition.
/-- Helper-stage boundedness from the scalar comparison and the
point-consistency `add-in-u` transfer.

This theorem composes the off-diagonal estimate supplied by
`pointConsistencyAddInUSelection` with
`helper_boundedness_gap_le_selfImprovementHelperError`.  It is the formal
statement of the sentence "combined with the explicit `A`-consistency bound" in the
boundedness paragraph of the self-improvement proof. -/
theorem helper_boundedness_gap_le_selfImprovementHelperError_of_pointConsistencyAddInU_transfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hZ_vs_H :
      ev strategy.state (helperUpperOperator params Z) -
          ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) ≤
        3 * Real.sqrt delta)
    (htransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          Hhat
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta) :
    helperBoundednessGap params strategy Hhat Z ≤
      selfImprovementHelperError params eps delta := by
  have hoffdiag_addInU :
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (Hhat.outcome h))) ≤ addInUError params eps delta :=
    pointConsistencyAddInU_off_diagonal_avg_le_of_transfer
      params strategy eps delta T Hhat htransfer
  have hoffdiag :
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (Hhat.outcome h))) ≤
        4 * Real.sqrt (selfImprovementVarianceError params eps delta) := by
    simpa [addInUError, Real.sqrt_eq_rpow] using hoffdiag_addInU
  exact
    helper_boundedness_gap_le_selfImprovementHelperError
      params strategy eps delta heps hdelta hZ_vs_H hoffdiag

-- This comparison transports the helper-completeness scalar through the
-- left/right tensor swap on the permutation-invariant state.
/-- Convert the helper-completeness `Hhat`-versus-`Z` comparison to the
right-placed total comparison used in the boundedness gap.

The helper-completeness paragraph naturally proves
`⟨ψ, Z ⊗ I⟩ - 3√δ ≤ subMeasMass ψ Hhat.liftLeft`. The boundedness decomposition,
however, uses the right-placed total `⟨ψ, I ⊗ Hhat.total⟩`. On the
permutation-invariant strategy state these scalars agree, so the comparison
becomes `⟨ψ, Z ⊗ I⟩ - ⟨ψ, I ⊗ Hhat.total⟩ ≤ 3√δ`. -/
theorem helper_upper_gap_rightTensor_le_three_sqrt_delta_of_helper_outputs
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z) :
    ev strategy.state (helperUpperOperator params Z) -
        ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) ≤
      3 * Real.sqrt delta := by
  have hleft :
      ev strategy.state (leftTensor (ι₂ := ι) Z) - 3 * Real.sqrt delta ≤
        subMeasMass strategy.state Hhat.liftLeft :=
    helper_hhat_vs_z_of_self_consistency_and_complementary_slackness
      params strategy eps delta hhelper hssc hslack
  have hmass :
      subMeasMass strategy.state Hhat.liftLeft =
        ev strategy.state (leftTensor (ι₂ := ι) Hhat.total) := rfl
  have hswap :
      ev strategy.state (leftTensor (ι₂ := ι) Hhat.total) =
        ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) :=
    strategy.permInvState.swap_ev Hhat.total
  unfold helperUpperOperator
  rw [hmass, hswap] at hleft
  linarith

/-- Helper-stage boundedness from the actual helper comparison and the
point-consistency `add-in-u` transfer.

This theorem composes the helper-completeness comparison `Hhat`-versus-`Z`
with the boundedness off-diagonal estimate. Complementary slackness remains an
explicit hypothesis because the reduced `SelfImprovementHelperConclusion`
records only the presently formalized SDP facts. The off-diagonal transfer is
likewise explicit: it is the formal statement of the `add-in-u` application
with `S_u = {(a,h) : h(u) ≠ a}`. -/
theorem helper_boundedness_gap_le_selfImprovementHelperError_of_helper_outputs
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z)
    (htransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          Hhat
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T.toSubMeas
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta) :
    helperBoundednessGap params strategy Hhat Z ≤
      selfImprovementHelperError params eps delta := by
  have hZ_vs_H :
      ev strategy.state (helperUpperOperator params Z) -
          ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) ≤
        3 * Real.sqrt delta :=
    helper_upper_gap_rightTensor_le_three_sqrt_delta_of_helper_outputs
      params strategy eps delta hhelper hssc hslack
  exact
    helper_boundedness_gap_le_selfImprovementHelperError_of_pointConsistencyAddInU_transfer
      params strategy eps delta heps hdelta hZ_vs_H htransfer

end MIPStarRE.LDT.SelfImprovement
