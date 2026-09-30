import MIPStarRE.LDT.Basic.ParametersFiniteAnswers
import MIPStarRE.LDT.Basic.OpFamily

/-!
# Section 12 — Definitions: tuples and operators

Tuple distributions, type abbreviations, and basic operator helpers.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The finite support of the distinct-tuple distribution. -/
noncomputable def distinctTupleSupport (params : Parameters) (k : ℕ) :
    Finset (PointTuple params k) := by
  classical
  exact Finset.univ.filter (fun xs : PointTuple params k => Function.Injective xs)

@[simp] theorem mem_distinctTupleSupport (params : Parameters) (k : ℕ)
    (xs : PointTuple params k) :
    xs ∈ distinctTupleSupport params k ↔ Function.Injective xs := by
  classical
  simp [distinctTupleSupport]

/-- The number of injective `k`-tuples is the falling factorial `q(q-1) ... (q-k+1)`. -/
theorem distinctTupleSupport_card (params : Parameters) (k : ℕ) :
    (distinctTupleSupport params k).card = params.q.descFactorial k := by
  classical
  rw [← Fintype.card_coe]
  let e : { xs : PointTuple params k // Function.Injective xs } ≃ (Fin k ↪ Fq params) :=
    Equiv.subtypeInjectiveEquivEmbedding (Fin k) (Fq params)
  simpa [distinctTupleSupport, Finset.mem_filter] using
    (Fintype.card_congr e).trans Fintype.card_embedding_eq

/-- If `k ≤ q`, there exists an injective `k`-tuple. -/
theorem distinctTupleSupport_nonempty_of_le
    (params : Parameters) (k : ℕ) (hk : k ≤ params.q) :
    (distinctTupleSupport params k).Nonempty := by
  classical
  refine ⟨fun i => ⟨i.1, Nat.lt_of_lt_of_le i.2 hk⟩, ?_⟩
  refine Finset.mem_filter.mpr ?_
  constructor
  · simp
  · intro i j hij
    exact Fin.ext (by simpa using congrArg Fin.val hij)

/-- If `q < k`, no injective `k`-tuple of field elements exists. -/
theorem distinctTupleSupport_eq_empty_of_lt
    (params : Parameters) (k : ℕ) (hk : params.q < k) :
    distinctTupleSupport params k = ∅ := by
  apply Finset.card_eq_zero.mp
  rw [distinctTupleSupport_card]
  exact Nat.descFactorial_eq_zero_iff_lt.mpr hk

/-- Uniform distribution on pairwise-distinct `k`-tuples from `Fq`.
Support is the set of injective functions `Fin k → Fq params`;
weight is uniform `1 / |support|` on support, `0` outside. -/
noncomputable def distinctTupleDistribution (params : Parameters) (k : ℕ) :
    Distribution (PointTuple params k) :=
  Distribution.uniformOnFinset (distinctTupleSupport params k)

@[simp] theorem distinctTupleDistribution_support (params : Parameters) (k : ℕ) :
    (distinctTupleDistribution params k).support = distinctTupleSupport params k := by
  simp [distinctTupleDistribution]

/-- For `k ≤ q`, the distinct-tuple distribution is a probability distribution. -/
theorem distinctTupleDistribution_isProbability_of_le
    (params : Parameters) (k : ℕ) (hk : k ≤ params.q) :
    (distinctTupleDistribution params k).IsProbability := by
  simpa [distinctTupleDistribution] using
    Distribution.uniformOnFinset_isProbability (distinctTupleSupport params k)
      (distinctTupleSupport_nonempty_of_le params k hk)

/-- The outcome type of the completed family `\widehat G`. -/
abbrev GHatOutcome (params : Parameters) [FieldModel params.q] := Option (Polynomial params)

/-- The question type for a single slice height. -/
abbrev SliceQuestion (params : Parameters) := Fq params

/-- The outcome type of a `k`-tuple of completed-slice answers. -/
abbrev GHatTupleOutcome (params : Parameters) [FieldModel params.q] (k : ℕ) :=
  Fin k → GHatOutcome params

/-- A sandwiched-line question consists of a point and a `k`-tuple of slice heights. -/
abbrev SandwichedLineQuestion (params : Parameters) (k : ℕ) :=
  Point params × PointTuple params k

/-- The question type for vertical lines, identified with their base point. -/
abbrev VerticalLineQuestion (params : Parameters) := Point params

/-- The support of a completed-slice tuple, i.e. the indices whose outcomes are
genuine polynomials rather than `⊥`. This matches the paper's support of the type
`τ ∈ {0,1}^k`. -/
def gHatTupleSupport {params : Parameters} {k : ℕ}
    [FieldModel params.q]
    (gs : GHatTupleOutcome params k) : Finset (Fin k) :=
  Finset.univ.filter fun i => (gs i).isSome

/-- The Hamming weight of a completed-slice tuple. -/
def gHatTupleHammingWeight {params : Parameters} {k : ℕ}
    [FieldModel params.q]
    (gs : GHatTupleOutcome params k) : ℕ :=
  (gHatTupleSupport gs).card

/-- A completed-slice tuple is eligible for interpolation exactly when its type has
Hamming weight at least `d + 1`, matching the paper's `|w| ≥ d+1` filter. -/
def InterpolationEligible (params : Parameters) {k : ℕ}
    [FieldModel params.q]
    (gs : GHatTupleOutcome params k) : Prop :=
  params.d + 1 ≤ gHatTupleHammingWeight gs

end MIPStarRE.LDT.Pasting
