import MIPStarRE.LDT.Preliminaries.CauchySchwarz

/-!
# Triangle Inequalities for State-Dependent Distance: Core

This module contains the main triangle-substitution estimates for approximate
measurements.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- Symmetry of the question-level state-dependent distance. -/
lemma qSDD_symm
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (A B : SubMeas Outcome ι) :
    qSDD ψ A B = qSDD ψ B A := by
  let F : Outcome → MIPStarRE.Quantum.Op ι := fun a => A.outcome a - B.outcome a
  let G : Outcome → MIPStarRE.Quantum.Op ι := fun a => B.outcome a - A.outcome a
  have hFG : F = fun a => -G a := by
    funext a
    dsimp [F, G]
    abel
  unfold qSDD qSDDCore
  change ∑ a : Outcome, ev ψ ((F a)ᴴ * F a) = ∑ a : Outcome, ev ψ ((G a)ᴴ * G a)
  rw [hFG]
  refine Finset.sum_congr rfl ?_
  intro a _
  change
    ev ψ ((-G a)ᴴ * (-G a)) = ev ψ ((G a)ᴴ * G a)
  simp

/-- Symmetry of the state-dependent distance relation. -/
lemma sddRel_symm
    {Question Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) (δ : Error) :
    SDDRel ψ 𝒟 A B δ →
      SDDRel ψ 𝒟 B A δ := by
  intro ⟨h⟩
  constructor
  simpa [sddError, qSDD_symm] using h

/-! ### Elementary max bound -/

/-- Adding `y` inside `max 0` changes the value by at most `|y|`. -/
lemma max_zero_add_le (x y : Error) :
    max 0 (x + y) ≤ max 0 x + |y| := by
  by_cases hxy : x + y < 0
  · rw [max_eq_left_of_lt hxy]
    positivity
  · have hxy' : 0 ≤ x + y := le_of_not_gt hxy
    rw [max_eq_right hxy']
    have hx : x ≤ max 0 x := le_max_right _ _
    have hy : y ≤ |y| := le_abs_self y
    linarith

private lemma avgOver_abs_le_sqrt_of_pointwise_nonneg
    {Question : Type*}
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (f g : Question → Error)
    (hfg : ∀ q, |f q| ≤ Real.sqrt (g q))
    (hg : ∀ q, 0 ≤ g q) :
    avgOver 𝒟 (fun q => |f q|) ≤ Real.sqrt (avgOver 𝒟 g) := by
  have havg_nonneg : 0 ≤ avgOver 𝒟 (fun q => |f q|) :=
    avgOver_nonneg 𝒟 (fun q => |f q|) (fun q => abs_nonneg (f q))
  have havg_abs :
      |avgOver 𝒟 (fun q => |f q|)| ≤ Real.sqrt (avgOver 𝒟 g) := by
    exact
      avgOver_abs_le_sqrt_of_pointwise 𝒟
        (fun q => |f q|)
        g
        (fun q => by
          simpa [abs_of_nonneg (abs_nonneg (f q))] using hfg q)
        hg
        h𝒟
  simpa [abs_of_nonneg havg_nonneg] using havg_abs

/-! ### Right-register variant of `triangleSub` -/

private lemma right_match_gap_abs_le_sqrt_qSDD
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (A B D : SubMeas Outcome ι) :
    |(∑ a : Outcome, ev ψ (A.outcome a * B.outcome a)) -
        ∑ a : Outcome, ev ψ (A.outcome a * D.outcome a)| ≤
      Real.sqrt (qSDD ψ B D) := by
  let diagA : Error := ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a)
  have hdiagA_le_one : diagA ≤ 1 := by
    simpa [diagA] using subMeas_diagMass_le_one ψ hψ A
  have haux :
      |∑ a : Outcome, ev ψ (A.outcome a * (B.outcome a - D.outcome a))| ≤
        Real.sqrt diagA * Real.sqrt (qSDD ψ B D) := by
    calc
      |∑ a : Outcome, ev ψ (A.outcome a * (B.outcome a - D.outcome a))|
        ≤ Real.sqrt
            (∑ a : Outcome, ev ψ (A.outcome a * (A.outcome a)ᴴ)) *
            Real.sqrt
              (∑ a : Outcome,
                ev ψ ((B.outcome a - D.outcome a)ᴴ *
                  (B.outcome a - D.outcome a))) := by
              simpa using
                sum_ev_mul_le_sqrt ψ
                  (fun a => A.outcome a)
                  (fun a => B.outcome a - D.outcome a)
      _ = Real.sqrt diagA * Real.sqrt (qSDD ψ B D) := by
            simp [diagA, qSDD, qSDDCore, SubMeas.outcome_hermitian]
  have hsqrtA : Real.sqrt diagA ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hdiagA_le_one
  have haux' :
      |∑ a : Outcome, ev ψ (A.outcome a * (B.outcome a - D.outcome a))| ≤
        Real.sqrt (qSDD ψ B D) := by
    calc
      |∑ a : Outcome, ev ψ (A.outcome a * (B.outcome a - D.outcome a))|
        ≤ Real.sqrt diagA * Real.sqrt (qSDD ψ B D) := haux
      _ ≤ 1 * Real.sqrt (qSDD ψ B D) := by
            exact mul_le_mul_of_nonneg_right hsqrtA (Real.sqrt_nonneg _)
      _ = Real.sqrt (qSDD ψ B D) := by ring
  convert haux' using 1
  refine congrArg abs ?_
  calc
    (∑ a : Outcome, ev ψ (A.outcome a * B.outcome a)) -
        ∑ a : Outcome, ev ψ (A.outcome a * D.outcome a)
      = ∑ a : Outcome,
          (ev ψ (A.outcome a * B.outcome a) -
            ev ψ (A.outcome a * D.outcome a)) := by
              rw [← Finset.sum_sub_distrib]
    _ = ∑ a : Outcome, ev ψ (A.outcome a * (B.outcome a - D.outcome a)) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [(ev_sub ψ (A.outcome a * B.outcome a)
            (A.outcome a * D.outcome a)).symm]
          simp [mul_sub]

theorem triangleSub_right
    {Question Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized) (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxSubMeas Question Outcome ι)
    (B D : IdxMeas Question Outcome ι) (δ ε : Error)
    (hAB : ConsRel ψ 𝒟
      A (IdxMeas.toIdxSubMeas B) δ)
    (hBD : SDDRel ψ 𝒟
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas D)) ε) :
    ConsRel ψ 𝒟
      A
      (IdxMeas.toIdxSubMeas D) (δ + Real.sqrt ε) := by
  let AL : IdxSubMeas Question Outcome (ι × ι) := IdxSubMeas.liftLeft A
  let BR : IdxSubMeas Question Outcome (ι × ι) :=
    IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)
  let DR : IdxSubMeas Question Outcome (ι × ι) :=
    IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas D)
  let matchB : Question → Error := fun q =>
    ∑ a : Outcome, ev ψ ((AL q).outcome a * (BR q).outcome a)
  let matchD : Question → Error := fun q =>
    ∑ a : Outcome, ev ψ ((AL q).outcome a * (DR q).outcome a)
  let overlap : Question → Error := fun q =>
    ev ψ (leftTensor (ι₂ := ι) ((A q).total))
  let sdd : Question → Error := fun q =>
    qSDD ψ (BR q) (DR q)
  let gap : Question → Error := fun q => matchB q - matchD q
  rcases hAB with ⟨hAB⟩
  rw [bipartiteConsError_eq_consError_placed] at hAB
  rcases hBD with ⟨hBD⟩
  have hgap_pointwise : ∀ q, |gap q| ≤ Real.sqrt (sdd q) := by
    intro q
    simpa [gap, matchB, matchD, sdd] using
      right_match_gap_abs_le_sqrt_qSDD ψ hψ (AL q) (BR q) (DR q)
  have hgap_avg_abs :
      avgOver 𝒟 (fun q => |gap q|) ≤ Real.sqrt (avgOver 𝒟 sdd) := by
    exact
      avgOver_abs_le_sqrt_of_pointwise_nonneg 𝒟 h𝒟 gap sdd
        hgap_pointwise
        (fun q => qSDD_nonneg ψ (BR q) (DR q))
  have hdefect_pointwise :
      ∀ q, qConsDefect ψ (AL q) (DR q) ≤ qConsDefect ψ (AL q) (BR q) + |gap q| := by
    intro q
    have hdefB :
        qConsDefect ψ (AL q) (BR q) = max 0 (overlap q - matchB q) := by
      unfold qConsDefect qMatchMass
      dsimp [overlap, matchB, AL, BR]
      rw [show
        ((IdxSubMeas.liftLeft A q).total) *
            ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B) q).total) =
          leftTensor (ι₂ := ι) ((A q).total) *
            rightTensor (ι₁ := ι) ((B q).total) by rfl]
      rw [(B q).total_eq_one]
      simp [IdxSubMeas.liftLeft, IdxSubMeas.liftRight, IdxMeas.toIdxSubMeas,
        leftTensor, rightTensor]
    have hdefD :
        qConsDefect ψ (AL q) (DR q) = max 0 (overlap q - matchD q) := by
      unfold qConsDefect qMatchMass
      dsimp [overlap, matchD, AL, DR]
      rw [show
        ((IdxSubMeas.liftLeft A q).total) *
            ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas D) q).total) =
          leftTensor (ι₂ := ι) ((A q).total) *
            rightTensor (ι₁ := ι) ((D q).total) by rfl]
      rw [(D q).total_eq_one]
      simp [IdxSubMeas.liftLeft, IdxSubMeas.liftRight, IdxMeas.toIdxSubMeas,
        leftTensor, rightTensor]
    calc
      qConsDefect ψ (AL q) (DR q)
        = max 0 ((overlap q - matchB q) + gap q) := by
            rw [hdefD]
            dsimp [gap]
            ring_nf
      _ ≤ max 0 (overlap q - matchB q) + |gap q| := max_zero_add_le _ _
      _ = qConsDefect ψ (AL q) (BR q) + |gap q| := by
            rw [hdefB]
  constructor
  rw [bipartiteConsError_eq_consError_placed]
  unfold consError sddError at *
  calc
    avgOver 𝒟 (fun q => qConsDefect ψ (AL q) (DR q))
      ≤ avgOver 𝒟 (fun q => qConsDefect ψ (AL q) (BR q) + |gap q|) := by
          apply avgOver_mono
          intro q
          exact hdefect_pointwise q
    _ = avgOver 𝒟 (fun q => qConsDefect ψ (AL q) (BR q)) +
          avgOver 𝒟 (fun q => |gap q|) := by
            rw [avgOver_add]
    _ ≤ δ + Real.sqrt (avgOver 𝒟 sdd) := by
          exact add_le_add hAB hgap_avg_abs
    _ ≤ δ + Real.sqrt ε := by
          simpa [add_comm] using add_le_add_right (Real.sqrt_le_sqrt hBD) δ

/-- Heterogeneous right-register substitution.

This is the same proof as `triangleSub_right`, with the left family placed on
`H_A` and the two right families placed on `H_B`.  It is the form needed for
the paper-facing two-prover strategy in `thm:main-formal`, where Alice's and
Bob's local Hilbert spaces are not assumed to be the same. -/
theorem triangleSub_right_heterogeneous
    {Question Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized) (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxSubMeas Question Outcome ιA)
    (B D : IdxMeas Question Outcome ιB) (δ ε : Error)
    (hAB : ConsRel ψ 𝒟
      A (IdxMeas.toIdxSubMeas B) δ)
    (hBD : SDDRel ψ 𝒟
      (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas B))
      (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas D)) ε) :
    ConsRel ψ 𝒟
      A
      (IdxMeas.toIdxSubMeas D) (δ + Real.sqrt ε) := by
  let AL : IdxSubMeas Question Outcome (ιA × ιB) :=
    IdxSubMeas.placeLeft (ιB := ιB) A
  let BR : IdxSubMeas Question Outcome (ιA × ιB) :=
    IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas B)
  let DR : IdxSubMeas Question Outcome (ιA × ιB) :=
    IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas D)
  let matchB : Question → Error := fun q =>
    ∑ a : Outcome, ev ψ ((AL q).outcome a * (BR q).outcome a)
  let matchD : Question → Error := fun q =>
    ∑ a : Outcome, ev ψ ((AL q).outcome a * (DR q).outcome a)
  let overlap : Question → Error := fun q =>
    ev ψ (leftTensor (ι₂ := ιB) ((A q).total))
  let sdd : Question → Error := fun q =>
    qSDD ψ (BR q) (DR q)
  let gap : Question → Error := fun q => matchB q - matchD q
  rcases hAB with ⟨hAB⟩
  rw [bipartiteConsError_eq_consError_placed] at hAB
  rcases hBD with ⟨hBD⟩
  have hgap_pointwise : ∀ q, |gap q| ≤ Real.sqrt (sdd q) := by
    intro q
    simpa [gap, matchB, matchD, sdd] using
      right_match_gap_abs_le_sqrt_qSDD ψ hψ (AL q) (BR q) (DR q)
  have hgap_avg_abs :
      avgOver 𝒟 (fun q => |gap q|) ≤ Real.sqrt (avgOver 𝒟 sdd) := by
    exact
      avgOver_abs_le_sqrt_of_pointwise_nonneg 𝒟 h𝒟 gap sdd
        hgap_pointwise
        (fun q => qSDD_nonneg ψ (BR q) (DR q))
  have hdefect_pointwise :
      ∀ q, qConsDefect ψ (AL q) (DR q) ≤ qConsDefect ψ (AL q) (BR q) + |gap q| := by
    intro q
    have hdefB :
        qConsDefect ψ (AL q) (BR q) = max 0 (overlap q - matchB q) := by
      unfold qConsDefect qMatchMass
      dsimp [overlap, matchB, AL, BR]
      rw [show
        ((IdxSubMeas.placeLeft (ιB := ιB) A q).total) *
            ((IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas B) q).total) =
          leftTensor (ι₂ := ιB) ((A q).total) *
            rightTensor (ι₁ := ιA) ((B q).total) by rfl]
      rw [(B q).total_eq_one]
      simp [IdxSubMeas.placeLeft, IdxSubMeas.placeRight, IdxMeas.toIdxSubMeas,
        leftTensor, rightTensor]
    have hdefD :
        qConsDefect ψ (AL q) (DR q) = max 0 (overlap q - matchD q) := by
      unfold qConsDefect qMatchMass
      dsimp [overlap, matchD, AL, DR]
      rw [show
        ((IdxSubMeas.placeLeft (ιB := ιB) A q).total) *
            ((IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas D) q).total) =
          leftTensor (ι₂ := ιB) ((A q).total) *
            rightTensor (ι₁ := ιA) ((D q).total) by rfl]
      rw [(D q).total_eq_one]
      simp [IdxSubMeas.placeLeft, IdxSubMeas.placeRight, IdxMeas.toIdxSubMeas,
        leftTensor, rightTensor]
    calc
      qConsDefect ψ (AL q) (DR q)
        = max 0 ((overlap q - matchB q) + gap q) := by
            rw [hdefD]
            dsimp [gap]
            ring_nf
      _ ≤ max 0 (overlap q - matchB q) + |gap q| := max_zero_add_le _ _
      _ = qConsDefect ψ (AL q) (BR q) + |gap q| := by
            rw [hdefB]
  constructor
  rw [bipartiteConsError_eq_consError_placed]
  unfold consError sddError at *
  calc
    avgOver 𝒟 (fun q => qConsDefect ψ (AL q) (DR q))
      ≤ avgOver 𝒟 (fun q => qConsDefect ψ (AL q) (BR q) + |gap q|) := by
          apply avgOver_mono
          intro q
          exact hdefect_pointwise q
    _ = avgOver 𝒟 (fun q => qConsDefect ψ (AL q) (BR q)) +
          avgOver 𝒟 (fun q => |gap q|) := by
            rw [avgOver_add]
    _ ≤ δ + Real.sqrt (avgOver 𝒟 sdd) := by
          exact add_le_add hAB hgap_avg_abs
    _ ≤ δ + Real.sqrt ε := by
          simpa [add_comm] using add_le_add_right (Real.sqrt_le_sqrt hBD) δ

end MIPStarRE.LDT.Preliminaries
