import MIPStarRE.LDT.MakingMeasurementsProjective.Defs
import MIPStarRE.LDT.Test.Defs

/-!
# Section 5 — Statements

Statements for Naimark dilation, one-measurement Naimark, the
orthogonalization lemma, rounding to projectors, rank reduction, and completing
to measurement.

## Naimark dilation statements

The **one-measurement Naimark lemma** (`OneMeasNaimarkLemma`) is the
building block: any submeasurement can be dilated to a projective
submeasurement on a space enlarged by one auxiliary register.

The questionwise **Naimark interface** (`NaimarkStatement`) records the
per-question one-measurement dilations and their single-outcome marginal
preservation identities.  It is not the full tensor-product statement of
`\label{thm:naimark}`.

The source theorem form is recorded separately as
`NaimarkTensorProductCorrelationStatement` and
`naimarkTensorProductCorrelation`.  This statement contains the full
bipartite auxiliary-state and correlation-preservation conclusion of
`\label{thm:naimark}` in the projective-submeasurement form supplied by the
paper's one-measurement helper.  The proof is the tensor-product assembly
implemented in `NaimarkFull.lean`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

universe u v

/-! ### One-measurement Naimark statement -/

/-- Statement of the one-measurement Naimark lemma (Lemma 5.2).

For any submeasurement `M` on `Op d`, there exists a one-measurement
Naimark dilation on the enlarged space `Op (d × Option α)`. -/
def OneMeasNaimarkLemma (α : Type*) [Fintype α] [DecidableEq α]
    (d : Type*) [Fintype d] [DecidableEq d]
    (M : MIPStarRE.Quantum.Submeasurement α d) : Prop :=
  ∃ data : OneMeasNaimarkData α d, data.source = M

/-! ### Tensor-product Naimark source theorem -/

/-- The density matrix of `ψ ⊗ aux`, written in the register order used by the
paper's dilated measurements:
`(Alice × AliceAux) × (Bob × BobAux)`.

The source paper writes the dilated vector as
`\ket{\widehat{\psi}} = \ket{\psi} \otimes \ket{\mathsf{aux}}`.  Since the
local dilated measurements act on `Alice × AliceAux` and `Bob × BobAux`, the
matrix entries below are the corresponding tensor-product density after the
canonical reassociation and permutation of the four finite registers. -/
noncomputable def naimarkProductExtensionDensity
    (HA HB : FiniteHilbertSpace.{u})
    (HauxA HauxB : FiniteHilbertSpace.{v})
    (ψ : QuantumState (HA.carrier × HB.carrier))
    (aux : QuantumState (HauxA.carrier × HauxB.carrier)) :
    MIPStarRE.Quantum.Op
      ((HA.carrier × HauxA.carrier) × (HB.carrier × HauxB.carrier)) :=
  fun r c =>
    ψ.density (r.1.1, r.2.1) (c.1.1, c.2.1) *
      aux.density (r.1.2, r.2.2) (c.1.2, c.2.2)

/-- The canonical register permutation from
`(Alice × Bob) × (AliceAux × BobAux)` to
`(Alice × AliceAux) × (Bob × BobAux)`. -/
def naimarkProductExtensionEquiv
    (HA HB : FiniteHilbertSpace.{u})
    (HauxA HauxB : FiniteHilbertSpace.{v}) :
    ((HA.carrier × HB.carrier) × (HauxA.carrier × HauxB.carrier)) ≃
      ((HA.carrier × HauxA.carrier) × (HB.carrier × HauxB.carrier)) :=
  Equiv.prodProdProdComm HA.carrier HB.carrier HauxA.carrier HauxB.carrier

/-- The product-extension density is the ordinary tensor-product density after
the register permutation used by the dilated measurements. -/
theorem naimarkProductExtensionDensity_eq_reindex_opTensor
    (HA HB : FiniteHilbertSpace.{u})
    (HauxA HauxB : FiniteHilbertSpace.{v})
    (ψ : QuantumState (HA.carrier × HB.carrier))
    (aux : QuantumState (HauxA.carrier × HauxB.carrier)) :
    naimarkProductExtensionDensity HA HB HauxA HauxB ψ aux =
      Matrix.reindex (naimarkProductExtensionEquiv HA HB HauxA HauxB)
        (naimarkProductExtensionEquiv HA HB HauxA HauxB)
        (opTensor ψ.density aux.density) := by
  ext r c
  rfl

/-- The product-extension density is positive semidefinite. -/
theorem naimarkProductExtensionDensity_nonneg
    (HA HB : FiniteHilbertSpace.{u})
    (HauxA HauxB : FiniteHilbertSpace.{v})
    (ψ : QuantumState (HA.carrier × HB.carrier))
    (aux : QuantumState (HauxA.carrier × HauxB.carrier)) :
    0 ≤ naimarkProductExtensionDensity HA HB HauxA HauxB ψ aux := by
  rw [naimarkProductExtensionDensity_eq_reindex_opTensor]
  exact MIPStarRE.Quantum.reindex_nonneg (naimarkProductExtensionEquiv HA HB HauxA HauxB)
    (opTensor_nonneg ψ.density_psd aux.density_psd)

/-- The quantum state `ψ ⊗ aux` in the register order used by the full Naimark
correlation theorem. -/
noncomputable def naimarkProductExtensionState
    (HA HB : FiniteHilbertSpace.{u})
    (HauxA HauxB : FiniteHilbertSpace.{v})
    (ψ : QuantumState (HA.carrier × HB.carrier))
    (aux : QuantumState (HauxA.carrier × HauxB.carrier)) :
    QuantumState ((HA.carrier × HauxA.carrier) × (HB.carrier × HauxB.carrier)) where
  density := naimarkProductExtensionDensity HA HB HauxA HauxB ψ aux
  density_psd := naimarkProductExtensionDensity_nonneg HA HB HauxA HauxB ψ aux

@[simp] theorem naimarkProductExtensionState_density
    (HA HB : FiniteHilbertSpace.{u})
    (HauxA HauxB : FiniteHilbertSpace.{v})
    (ψ : QuantumState (HA.carrier × HB.carrier))
    (aux : QuantumState (HauxA.carrier × HauxB.carrier)) :
    (naimarkProductExtensionState HA HB HauxA HauxB ψ aux).density =
      naimarkProductExtensionDensity HA HB HauxA HauxB ψ aux := rfl

/-- The product-extension state is normalized whenever both tensor factors are
normalized. -/
theorem naimarkProductExtensionState_isNormalized
    (HA HB : FiniteHilbertSpace.{u})
    (HauxA HauxB : FiniteHilbertSpace.{v})
    {ψ : QuantumState (HA.carrier × HB.carrier)}
    {aux : QuantumState (HauxA.carrier × HauxB.carrier)}
    (hψ : ψ.IsNormalized) (haux : aux.IsNormalized) :
    (naimarkProductExtensionState HA HB HauxA HauxB ψ aux).IsNormalized := by
  have hsource :
      (QuantumState.tensor ψ aux).IsNormalized :=
    QuantumState.tensor_isNormalized hψ haux
  rw [QuantumState.IsNormalized, naimarkProductExtensionState_density,
    naimarkProductExtensionDensity_eq_reindex_opTensor,
    MIPStarRE.Quantum.normalizedTrace_reindex]
  simpa [QuantumState.IsNormalized] using hsource

/-! ### Orthonormalization statements -/

/-- Paper origin: `references/ldt-paper/preliminaries.tex:348-376`
(`\label{def:approx_delta}`) and `references/ldt-paper/orthonormalization.tex`
§4 prose around `\label{lem:projective-non-measurement}` (lines 414-538).

Conclusion of the intermediate almost-projective step: a measurement which is
ζ-strongly self-consistent and ζ-self-close in the state-dependent distance,
and whose effects satisfy `Σₐ (Aₐ − Aₐ²) ≤ ζ`. -/
structure AlmostProjMeasStatement {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) : Prop where
  strongSelfConsistency :
    SSCRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas) ζ
  selfDistance :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily A.toSubMeas)
      (2 * ζ)
  sourceAlmostProjective :
    ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ ζ

end MIPStarRE.LDT.MakingMeasurementsProjective
