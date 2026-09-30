import MIPStarRE.LDT.MakingMeasurementsProjective.NaimarkOneMeas

/-!
# Section 5 — Naimark tensor-product assembly

Questionwise one-measurement Naimark data, the two-sided trace identity, and
the source-facing tensor-product Naimark theorem in the projective-submeasurement
form supplied by the paper's helper lemma.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

universe u v

private theorem idxSubMeas_outcome_sum_le_one
    {Question Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxSubMeas Question Outcome ι) (x : Question) :
    ∑ a, (A x).outcome a ≤ 1 := by
  simpa [(A x).sum_eq_total] using (A x).total_le_one

/-! ### Questionwise Naimark dilation interface -/

/-- The one-measurement Naimark dilation attached to a single question.

Paper origin: this is the questionwise application of
`references/ldt-paper/orthonormalization.tex:121-159`
(`\label{lem:naimark-helper}`) used in the proof of
`references/ldt-paper/orthonormalization.tex:36-80`
(`\label{thm:naimark}`), specifically the tensor-product assembly at
`references/ldt-paper/orthonormalization.tex:161-187`. -/
noncomputable def questionwiseOneMeasNaimarkData
    {Question Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι]
    (A : IdxSubMeas Question Outcome ι) (x : Question) :
    OneMeasNaimarkData Outcome ι :=
  Classical.choose <| oneMeasNaimark ({
    effect := (A x).outcome
    pos := (A x).outcome_pos
    sum_le_one := idxSubMeas_outcome_sum_le_one A x
  } : MIPStarRE.Quantum.Submeasurement Outcome ι)

/-- The questionwise Naimark data is attached to the intended source
submeasurement. -/
theorem questionwiseOneMeasNaimarkData_source_effect
    {Question Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι]
    (A : IdxSubMeas Question Outcome ι) (x : Question) :
    (questionwiseOneMeasNaimarkData A x).source.effect = (A x).outcome := by
  simpa [questionwiseOneMeasNaimarkData] using
    congrArg MIPStarRE.Quantum.Submeasurement.effect <|
      Classical.choose_spec <| oneMeasNaimark ({
        effect := (A x).outcome
        pos := (A x).outcome_pos
        sum_le_one := idxSubMeas_outcome_sum_le_one A x
      } : MIPStarRE.Quantum.Submeasurement Outcome ι)

/-! ### Full tensor-product Naimark interface -/

/-- The single auxiliary Hilbert space used by the full Naimark assembly on one side.

The one-measurement theorem produces projectors on `H × Option Outcome`.  Since
all questions on one side have the same outcome type, the different question
measurements may be represented on the same auxiliary space, with a different
Naimark unitary for each question. -/
def oneNaimarkAuxHilbertSpace (Outcome : Type u)
    [Fintype Outcome] [DecidableEq Outcome] :
    FiniteHilbertSpace.{u} where
  carrier := Option Outcome
  instFintype := inferInstance
  instDecidableEq := inferInstance
  instNonempty := ⟨none⟩

/-- The distinguished auxiliary basis state `|⊥⟩` for the one-register Naimark
assembly. -/
noncomputable def oneNaimarkAuxPureState (Outcome : Type u)
    [Fintype Outcome] [DecidableEq Outcome] :
    PureState (oneNaimarkAuxHilbertSpace Outcome).carrier :=
  PureState.basis (none : Option Outcome)

/-- The normalized auxiliary density state `|⊥⟩⟨⊥|`. -/
noncomputable def oneNaimarkAuxState (Outcome : Type u)
    [Fintype Outcome] [DecidableEq Outcome] :
    QuantumState (oneNaimarkAuxHilbertSpace Outcome).carrier :=
  oneNaimarkAuxPureState Outcome

/-- The one-register auxiliary state is normalized. -/
theorem oneNaimarkAuxState_isNormalized (Outcome : Type u)
    [Fintype Outcome] [DecidableEq Outcome] :
    (oneNaimarkAuxState Outcome).IsNormalized := by
  exact PureState.toQuantumState_isNormalized (oneNaimarkAuxPureState Outcome)

/-- The one-measurement preservation identity identifies the `⊥,⊥`
compression block of the dilated projector with the original effect. -/
theorem OneMeasNaimarkData.compression_none_none
    {Outcome : Type u} [Fintype Outcome] [DecidableEq Outcome]
    {d : Type v} [Fintype d] [DecidableEq d]
    (data : OneMeasNaimarkData Outcome d) (a : Outcome) (i j : d) :
    data.liftedEffect (some a) (i, none) (j, none) =
      data.source.effect a i j := by
  classical
  letI : Nonempty d := ⟨i⟩
  have h := data.expectation_preservation (Matrix.single j i (1 : ℂ)) a
  unfold oneMeasLiftedDensity MIPStarRE.Quantum.normalizedTrace at h
  simp [Matrix.trace, Matrix.mul_apply, Matrix.kronecker, naimarkAuxProjector,
    Matrix.single, Fintype.sum_prod_type] at h
  have hd : (Fintype.card d : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hOutcome : (Fintype.card (Option Outcome) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp [hd, hOutcome] at h
  have hsum_if_pair_eq :
      ∀ F : d → d → ℂ,
        (∑ x : d, ∑ y : d, if j = x ∧ i = y then F y x else 0) = F i j := by
    intro F
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single i]
      · simp
      · intro y _ hyi
        simp [show i ≠ y by exact fun h => hyi h.symm]
      · intro hi
        simp at hi
    · intro x _ hxj
      simp [show j ≠ x by exact fun h => hxj h.symm]
    · intro hj
      simp at hj
  rw [hsum_if_pair_eq (fun y x => data.source.effect a y x)] at h
  rw [← Finset.mul_sum] at h
  rw [hsum_if_pair_eq (fun y x => data.liftedEffect (some a) (y, none) (x, none))] at h
  have hc : (↑(Fintype.card Outcome) + 1 : ℂ) ≠ 0 := by
    positivity
  exact mul_left_cancel₀ hc (by
    calc
      (↑(Fintype.card Outcome) + 1 : ℂ) *
          data.liftedEffect (some a) (i, none) (j, none) =
        data.source.effect a i j * (↑(Fintype.card Outcome) + 1 : ℂ) := h.symm
      _ = (↑(Fintype.card Outcome) + 1 : ℂ) * data.source.effect a i j := by ring)

/-- The two-sided trace identity for the full tensor-product Naimark assembly.

Paper origin: `references/ldt-paper/orthonormalization.tex:161-187`, where the
one-measurement helper is applied on Alice's and Bob's sides and then tensored
with the auxiliary state.  The one-measurement theorem already gives the local
compression identity for every test operator.  The statement below isolates the
standard four-register trace calculation which turns the two local compression
identities into preservation of bipartite correlations. -/
theorem OneMeasNaimarkData.twoSidedCorrelationPreservation
    {OutcomeA OutcomeB : Type v}
    [Fintype OutcomeA] [DecidableEq OutcomeA]
    [Fintype OutcomeB] [DecidableEq OutcomeB]
    (HA HB : FiniteHilbertSpace.{u})
    (ψ : QuantumState (HA.carrier × HB.carrier))
    (leftData : OneMeasNaimarkData OutcomeA HA.carrier)
    (rightData : OneMeasNaimarkData OutcomeB HB.carrier)
    (a : OutcomeA) (b : OutcomeB) :
    ev ψ (opTensor (leftData.source.effect a) (rightData.source.effect b)) =
      ev
        (naimarkProductExtensionState HA HB
          (oneNaimarkAuxHilbertSpace OutcomeA)
          (oneNaimarkAuxHilbertSpace OutcomeB)
          ψ
          (QuantumState.tensor
            (oneNaimarkAuxState OutcomeA)
            (oneNaimarkAuxState OutcomeB)))
        (opTensor
          ((leftData.toProjSubMeas).outcome a)
          ((rightData.toProjSubMeas).outcome b)) := by
  classical
  have hleft_comp :
      ∀ i j : HA.carrier,
        leftData.liftedEffect (some a) (i, none) (j, none) =
          leftData.source.effect a i j :=
    OneMeasNaimarkData.compression_none_none leftData a
  have hright_comp :
      ∀ i j : HB.carrier,
        rightData.liftedEffect (some b) (i, none) (j, none) =
          rightData.source.effect b i j :=
    OneMeasNaimarkData.compression_none_none rightData b
  unfold ev
  congr 1
  unfold MIPStarRE.Quantum.normalizedTrace
  simp [naimarkProductExtensionState, naimarkProductExtensionDensity,
    QuantumState.tensor, oneNaimarkAuxState, oneNaimarkAuxPureState,
    PureState.density, pureDensity, PureState.basis, Matrix.mul_apply,
    Matrix.trace, opTensor, Matrix.kronecker, Matrix.vecMulVec]
  simp [Fintype.sum_prod_type, OneMeasNaimarkData.toProjSubMeas,
    mul_assoc, mul_left_comm, mul_comm]
  field_simp
  let cA : ℂ := Fintype.card (oneNaimarkAuxHilbertSpace OutcomeA).carrier
  let cB : ℂ := Fintype.card (oneNaimarkAuxHilbertSpace OutcomeB).carrier
  let S : ℂ :=
    ∑ x : HA.carrier,
      ∑ x_1 : HB.carrier,
        ∑ x_2 : HA.carrier,
          ∑ x_3 : HB.carrier,
            ψ.density (x, x_1) (x_2, x_3) *
              leftData.source.effect a x_2 x *
              rightData.source.effect b x_3 x_1
  change S * cA * cB =
    ∑ x : HA.carrier,
      ∑ x_1 : HB.carrier,
        ∑ x_2 : HA.carrier,
          ∑ x_3 : HB.carrier,
            cA * cB * ψ.density (x, x_1) (x_2, x_3) *
              leftData.liftedEffect (some a) (x_2, none) (x, none) *
              rightData.liftedEffect (some b) (x_3, none) (x_1, none)
  rw [show
      (∑ x : HA.carrier,
        ∑ x_1 : HB.carrier,
          ∑ x_2 : HA.carrier,
            ∑ x_3 : HB.carrier,
              cA * cB * ψ.density (x, x_1) (x_2, x_3) *
                leftData.liftedEffect (some a) (x_2, none) (x, none) *
                rightData.liftedEffect (some b) (x_3, none) (x_1, none)) =
        cA * cB * S by
      calc
        (∑ x : HA.carrier,
          ∑ x_1 : HB.carrier,
            ∑ x_2 : HA.carrier,
              ∑ x_3 : HB.carrier,
                cA * cB * ψ.density (x, x_1) (x_2, x_3) *
                  leftData.liftedEffect (some a) (x_2, none) (x, none) *
                  rightData.liftedEffect (some b) (x_3, none) (x_1, none))
            = ∑ x : HA.carrier,
              ∑ x_1 : HB.carrier,
                ∑ x_2 : HA.carrier,
                  ∑ x_3 : HB.carrier,
                    cA * cB *
                      (ψ.density (x, x_1) (x_2, x_3) *
                        leftData.source.effect a x_2 x *
                        rightData.source.effect b x_3 x_1) := by
              refine Finset.sum_congr rfl ?_
              intro x _
              refine Finset.sum_congr rfl ?_
              intro x_1 _
              refine Finset.sum_congr rfl ?_
              intro x_2 _
              refine Finset.sum_congr rfl ?_
              intro x_3 _
              rw [hleft_comp x_2 x, hright_comp x_3 x_1]
              ring
        _ = cA * cB * S := by
              simp [S, mul_assoc, Finset.mul_sum]]
  ring_nf

end MIPStarRE.LDT.MakingMeasurementsProjective
