import MIPStarRE.LDT.Pasting.ComparisonLemmas.LdSandwichLineOnePoint.Endpoint

/-!
# Section 12 pasting: line one-point transport — prefix moved lemmas

Internal helper module; part of the file-split for `#1127`.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The original one-point left family restricted to the prefix through coordinate `i`. -/
noncomputable def ldSandwichLineOnePointPrefixOriginalFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) ι :=
  fun q =>
    let xs : PointTuple params (i + 1) := fun j => q.2 ⟨j.1, by omega⟩
    postprocess
      (restrictSubMeas (gHatSandwichFamily params family (i + 1) xs)
        (fun gs => (gs ⟨i, Nat.lt_succ_self i⟩).isSome = true))
      (fun gs => Option.map (fun g : Polynomial params => g q.1)
        (gs ⟨i, Nat.lt_succ_self i⟩))

/-- The prefix family after rotating the selected coordinate to the front. -/
noncomputable def ldSandwichLineOnePointPrefixMovedFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) ι :=
  fun q =>
    let xsTail : PointTuple params i := fun j => q.2 ⟨j.1, by omega⟩
    let xs : PointTuple params (i + 1) := Fin.cons (q.2 ⟨i, hi⟩) xsTail
    postprocess
      (restrictSubMeas (gHatSandwichFamily params family (i + 1) xs)
        (fun gs => (gs 0).isSome = true))
      (fun gs => Option.map (fun g : Polynomial params => g q.1) (gs 0))

/-- Rotating the selected coordinate to the front reduces the prefix family to the
slice--vertical-line consistency relation `eq:ld-gbcon`.

This is the prefix-completeness collapse and endpoint identification used after
`references/ldt-paper/ld-pasting.tex:1011--1024`: once the selected coordinate is
first, summing the remaining prefix sandwich leaves the one-point endpoint
measurement. -/
lemma ldSandwichLineOnePointPrefixMoved_eq_endpoint
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    ldSandwichLineOnePointPrefixMovedFamily params family hi =
      (fun q : SandwichedLineQuestion params k =>
        postprocess
          (evaluateAt params q.1 ((family.meas (q.2 ⟨i, hi⟩)).toSubMeas))
          some) := by
  funext q
  let xsTail : PointTuple params i := fun j => q.2 ⟨j.1, by omega⟩
  let xs : PointTuple params (i + 1) := Fin.cons (q.2 ⟨i, hi⟩) xsTail
  have hzero := ldSandwichLineOnePointLeftFamily_zero_eq_endpoint
    (params := params) (strategy := strategy) (family := family)
    (k := i + 1) (hk := Nat.succ_pos i)
  let hq : SandwichedLineQuestion params (i + 1) := (q.1, xs)
  have hlocal :
      (ldSandwichLineOnePointLeftFamily params strategy family (i + 1) 0) hq =
        postprocess
          (evaluateAt params hq.1 ((family.meas (hq.2 ⟨0, Nat.succ_pos i⟩)).toSubMeas))
          some := by
    simpa using congrFun hzero hq
  simpa [ldSandwichLineOnePointPrefixMovedFamily, ldSandwichLineOnePointLeftFamily,
    hq, xs, xsTail] using hlocal

/-- The global one-point left family at its last prefix index is the prefix family. -/
lemma ldSandwichLineOnePointLeftFamily_self_eq_prefixOriginal
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (i : ℕ) :
    ldSandwichLineOnePointLeftFamily params strategy family (i + 1) i =
      ldSandwichLineOnePointPrefixOriginalFamily params family (Nat.lt_succ_self i) := by
  funext q
  simp [ldSandwichLineOnePointLeftFamily, ldSandwichLineOnePointPrefixOriginalFamily]

/-- Endpoint consistency for the rotated prefix family. -/
lemma ldSandwichLineOnePointPrefixMoved_consRel_endpoint_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta zeta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    {k i : ℕ} (hi : i < k) :
    ConsRel strategy.state
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointPrefixMovedFamily params family hi)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
  have hend := ldSandwichLineOnePoint_endpoint_ldGbcon_lift_of_axis_self
    params strategy eps delta zeta haxis hself family hcons k i hi
  simpa [ldSandwichLineOnePointPrefixMoved_eq_endpoint params strategy family hi] using hend

/-- Expand a half-product into the prefix product times the last slice operator. -/
lemma gHatHalfProduct_prefix_mul_last
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ i (xs : PointTuple params (i + 2)) (gs : GHatTupleOutcome params (i + 2)),
      gHatHalfProductOutcomeOperator params family (i + 2) xs gs =
        gHatHalfProductOutcomeOperator params family (i + 1)
            (fun j => xs ⟨j.1, by omega⟩)
            (fun j => gs ⟨j.1, by omega⟩) *
          (gHatIdxMeas params family (xs ⟨i + 1, by omega⟩)).outcome
            (gs ⟨i + 1, by omega⟩) := by
  intro i
  induction i with
  | zero =>
      intro xs gs
      simp [gHatHalfProductOutcomeOperator, pointTupleTail, gHatTupleOutcomeTail]
  | succ i ih =>
      intro xs gs
      have htail := ih (pointTupleTail xs) (gHatTupleOutcomeTail gs)
      rw [gHatHalfProductOutcomeOperator]
      rw [htail]
      simp [gHatHalfProductOutcomeOperator, pointTupleTail, gHatTupleOutcomeTail, mul_assoc]
      congr

/-- Split the ordered half-product into its first `n` coordinates and the last slice. -/
lemma gHatHalfProductOutcomeOperator_prefix_last
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ n (xs : PointTuple params (n + 1)) (gs : GHatTupleOutcome params (n + 1)),
      gHatHalfProductOutcomeOperator params family (n + 1) xs gs =
        gHatHalfProductOutcomeOperator params family n
            (fun j => xs ⟨j.1, by omega⟩)
            (fun j => gs ⟨j.1, by omega⟩) *
          (gHatIdxMeas params family (xs ⟨n, Nat.lt_succ_self n⟩)).outcome
            (gs ⟨n, Nat.lt_succ_self n⟩)
  | 0, xs, gs => by
      simp [gHatHalfProductOutcomeOperator]
  | n + 1, xs, gs => by
      simpa using gHatHalfProduct_prefix_mul_last params family n xs gs

/-- Summing the last completed-slice sandwich coordinate deletes that coordinate.

This formalizes the measurement-completeness step in `ld-pasting.tex`
lines 934--941 for a single trailing coordinate. -/
lemma gHatSandwich_sum_last_eq_prefix
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (n : ℕ) (xs : PointTuple params (n + 1))
    (gsPrefix : GHatTupleOutcome params n) :
    (∑ g : GHatOutcome params,
      let half := gHatHalfProductOutcomeOperator params family (n + 1) xs
        ((gHatTupleOutcomePrefixLastEquiv params n).symm (gsPrefix, g))
      half * halfᴴ) =
      gHatHalfProductOutcomeOperator params family n
        (fun j => xs ⟨j.1, by omega⟩) gsPrefix *
        (gHatHalfProductOutcomeOperator params family n
          (fun j => xs ⟨j.1, by omega⟩) gsPrefix)ᴴ := by
  let P : MIPStarRE.Quantum.Op ι :=
    gHatHalfProductOutcomeOperator params family n
      (fun j => xs ⟨j.1, by omega⟩) gsPrefix
  let G : GHatOutcome params → MIPStarRE.Quantum.Op ι := fun g =>
    (gHatIdxMeas params family (xs ⟨n, Nat.lt_succ_self n⟩)).outcome g
  have hsumG : (∑ g : GHatOutcome params, G g) = 1 := by
    dsimp [G]
    rw [(gHatIdxMeas params family (xs ⟨n, Nat.lt_succ_self n⟩)).sum_eq_total]
    simp [gHatIdxMeas, completeSubMeas]
  have hsumGG : (∑ g : GHatOutcome params, G g * (G g)ᴴ) = 1 := by
    calc
      (∑ g : GHatOutcome params, G g * (G g)ᴴ)
          = ∑ g : GHatOutcome params, G g := by
            refine Finset.sum_congr rfl ?_
            intro g _hg
            have hherm : (G g)ᴴ = G g := by
              simpa [G] using
                (gHatIdxMeas params family (xs ⟨n, Nat.lt_succ_self n⟩)).outcome_hermitian g
            have hproj : G g * G g = G g := by
              simpa [G] using
                gHatIdxMeas_proj params family (xs ⟨n, Nat.lt_succ_self n⟩) g
            simp [hherm, hproj]
      _ = 1 := hsumG
  have hinner : (∑ g : GHatOutcome params, (P * G g) * (P * G g)ᴴ) = P * Pᴴ := by
    calc
      (∑ g : GHatOutcome params, (P * G g) * (P * G g)ᴴ)
          = ∑ g : GHatOutcome params, P * (G g * (G g)ᴴ) * Pᴴ := by
            refine Finset.sum_congr rfl ?_
            intro g _hg
            simp [Matrix.conjTranspose_mul, mul_assoc]
      _ = P * (∑ g : GHatOutcome params, G g * (G g)ᴴ) * Pᴴ := by
            rw [← Finset.sum_mul, ← Matrix.mul_sum]
      _ = P * Pᴴ := by
            simp [hsumGG]
  calc
    (∑ g : GHatOutcome params,
      let half := gHatHalfProductOutcomeOperator params family (n + 1) xs
        ((gHatTupleOutcomePrefixLastEquiv params n).symm (gsPrefix, g))
      half * halfᴴ)
        = ∑ g : GHatOutcome params, (P * G g) * (P * G g)ᴴ := by
          refine Finset.sum_congr rfl ?_
          intro g _hg
          simp [P, G, gHatTupleOutcomePrefixLastEquiv,
            gHatHalfProductOutcomeOperator_prefix_last]
    _ = P * Pᴴ := hinner
    _ = gHatHalfProductOutcomeOperator params family n
          (fun j => xs ⟨j.1, by omega⟩) gsPrefix *
        (gHatHalfProductOutcomeOperator params family n
          (fun j => xs ⟨j.1, by omega⟩) gsPrefix)ᴴ := by
        rfl

end MIPStarRE.LDT.Pasting
