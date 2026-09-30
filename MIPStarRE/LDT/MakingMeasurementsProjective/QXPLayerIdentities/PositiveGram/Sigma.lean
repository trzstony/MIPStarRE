import Mathlib.Analysis.InnerProductSpace.GramMatrix
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerIdentities.PositiveGram.Completion

/-!
# Section 5 — Positive-Gram sigma-space specialization

Application of the positive-Gram polar construction to the canonical
sigma-space layer obtained from a rank-reduction witness.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

universe uOutcome uι

noncomputable section

/-- Explicit positive-Gram polar extension from chosen row-extension data with
the left factor represented as a unitary group element.

The existential construction of `Xhat` first chooses an embedding of the
positive spectral subspace into the auxiliary row space, then chooses a unitary
group element `U` extending the normalized image rows and a rectangular
coisometry `W` extending the right singular rows.  This theorem records the
deterministic matrix produced from those choices, namely `Uᵀ * W`, together
with the two QXP identities it satisfies.

The explicit form is useful when a later argument needs to impose additional
structure on the chosen rows, such as fresh option-completion row preservation
used to derive the QXP-internal comparison `Q_none ≤ P_none`. -/
theorem xHat_of_positive_gram_spectrum_unitaryGroup_choices
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hQ : Q.IsHermitian) (hQ_pos : Q.PosSemidef)
    (hgram : Xᴴ * X = Q)
    (e : {i : ι // 0 < hQ.eigenvalues i} ↪ μ)
    (U : Matrix.unitaryGroup μ ℂ) (W : Matrix μ ι ℂ)
    (hU_rows :
      ∀ (i : {i : ι // 0 < hQ.eigenvalues i}) (r : μ),
        (U : Matrix μ μ ℂ) (e i) r = positiveGramSpectrumImageRows X Q hQ i r)
    (hW : W * Wᴴ = (1 : Matrix μ μ ℂ))
    (hW_rows :
      ∀ (i : {i : ι // 0 < hQ.eigenvalues i}) (r : ι),
        W (e i) r = positiveGramSpectrumRightRows Q hQ i r) :
    ((U : Matrix μ μ ℂ)ᵀ * W) * ((U : Matrix μ μ ℂ)ᵀ * W)ᴴ =
        (1 : Matrix μ μ ℂ) ∧
      Xᴴ * ((U : Matrix μ μ ℂ)ᵀ * W) = CFC.sqrt Q := by
  constructor
  · exact transpose_unitaryGroup_mul_rectangular_coisometry U W hW
  · exact positive_gram_polar_extension_mixed_eq_sqrt_unitaryGroup X Q hQ hQ_pos
      hgram e U W hU_rows hW_rows

/-- Existence of the polar-extension `Xhat` from a positive Gram factorization.

If `Q = X†X` is positive semidefinite and the row dimension is at most the
column dimension, the positive spectral rows of `Q` determine a rectangular
coisometry `Xhat` satisfying the two primitive QXP identities:
`Xhat Xhat† = I` and `X† Xhat = sqrt Q`. -/
theorem exists_xHat_of_positive_gram_spectrum
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι]
    [NonUnitalContinuousFunctionalCalculus ℝ (Matrix ι ι ℂ) IsSelfAdjoint]
    (X : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hQ : Q.IsHermitian) (hQ_pos : Q.PosSemidef)
    (hgram : Xᴴ * X = Q)
    (hcard : Fintype.card μ ≤ Fintype.card ι) :
    ∃ xHat : Matrix μ ι ℂ,
      xHat * xHatᴴ = (1 : Matrix μ μ ℂ) ∧
        Xᴴ * xHat = CFC.sqrt Q := by
  classical
  obtain ⟨e, U, hU_rows⟩ :=
    exists_unitaryGroup_with_positive_gram_spectrum_rows_of_card X Q hQ hgram
  obtain ⟨W, hW, hW_rows⟩ :=
    exists_rectangular_coisometry_with_positive_gram_spectrum_right_rows Q hQ e hcard
  have hchoices := xHat_of_positive_gram_spectrum_unitaryGroup_choices
    X Q hQ hQ_pos hgram e U W hU_rows hW hW_rows
  refine ⟨(U : Matrix μ μ ℂ)ᵀ * W, ?_, ?_⟩
  · exact hchoices.1
  · exact hchoices.2

end

end MIPStarRE.LDT.MakingMeasurementsProjective
