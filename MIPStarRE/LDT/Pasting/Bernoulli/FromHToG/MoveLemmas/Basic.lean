import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Binomial
import MIPStarRE.LDT.Pasting.ComparisonLemmas.Common

/-!
# Section 12 pasting: from-H-to-G move lemmas

Tensor, positivity, and Cauchy--Schwarz helper lemmas for the adjacent paper chain.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Completed `ĝ` measurement outcomes are Hermitian.  This records the
positivity-to-Hermitian conversion used when orienting the adjoint
half-sandwich commutator in the `M₂ → M₃` move. -/
lemma fromHToG_gHatIdxMeas_outcome_isHermitian
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) (g : GHatOutcome params) :
    ((gHatIdxMeas params family x).outcome g)ᴴ =
      (gHatIdxMeas params family x).outcome g := by
  exact (Matrix.nonneg_iff_posSemidef.mp
    ((gHatIdxMeas params family x).outcome_pos g)).isHermitian.eq

/-- Reverse a tuple of slice questions. -/
def fromHToGPointTupleReverseEquiv (params : Parameters) (n : ℕ) :
    PointTuple params n ≃ PointTuple params n where
  toFun xs := fun i => xs i.rev
  invFun xs := fun i => xs i.rev
  left_inv xs := by
    funext i
    simp [Fin.rev_rev]
  right_inv xs := by
    funext i
    simp [Fin.rev_rev]

/-- Reverse a tuple of completed-slice outcomes. -/
def fromHToGGHatTupleOutcomeReverseEquiv
    (params : Parameters) [FieldModel params.q] (n : ℕ) :
    GHatTupleOutcome params n ≃ GHatTupleOutcome params n where
  toFun gs := fun i => gs i.rev
  invFun gs := fun i => gs i.rev
  left_inv gs := by
    funext i
    simp [Fin.rev_rev]
  right_inv gs := by
    funext i
    simp [Fin.rev_rev]

/-- Tail of a snoc tuple. -/
lemma fromHToG_pointTupleTail_snoc
    (params : Parameters) {n : ℕ}
    (xs : PointTuple params (n + 1)) (x : Fq params) :
    pointTupleTail (Fin.snoc xs x) = Fin.snoc (pointTupleTail xs) x := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · have hL : pointTupleTail (Fin.snoc xs x) (Fin.last n) = x := by
        change Fin.snoc (α := fun _ : Fin (n + 2) => Fq params) xs x
          (Fin.last (n + 1)) = x
        simp
    have hR :
        Fin.snoc (α := fun _ : Fin (n + 1) => Fq params) (pointTupleTail xs) x
          (Fin.last n) = x := by
      simp
    exact hL.trans hR.symm
  · intro j
    have hL : pointTupleTail (Fin.snoc xs x) j.castSucc = xs j.succ := by
      change Fin.snoc (α := fun _ : Fin (n + 2) => Fq params) xs x
        (j.succ.castSucc) = xs j.succ
      rw [Fin.snoc_castSucc]
    have hR :
        Fin.snoc (α := fun _ : Fin (n + 1) => Fq params) (pointTupleTail xs) x
          j.castSucc = xs j.succ := by
      rw [Fin.snoc_castSucc]
      rfl
    exact hL.trans hR.symm

/-- Tail of a snoc completed-outcome tuple. -/
lemma fromHToG_gHatTupleOutcomeTail_snoc
    (params : Parameters) [FieldModel params.q] {n : ℕ}
    (gs : GHatTupleOutcome params (n + 1)) (g : GHatOutcome params) :
    gHatTupleOutcomeTail (Fin.snoc gs g) = Fin.snoc (gHatTupleOutcomeTail gs) g := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · have hL : gHatTupleOutcomeTail (Fin.snoc gs g) (Fin.last n) = g := by
        change Fin.snoc (α := fun _ : Fin (n + 2) => GHatOutcome params) gs g
          (Fin.last (n + 1)) = g
        simp
    have hR :
        Fin.snoc (α := fun _ : Fin (n + 1) => GHatOutcome params)
          (gHatTupleOutcomeTail gs) g (Fin.last n) = g := by
      simp
    exact hL.trans hR.symm
  · intro j
    have hL : gHatTupleOutcomeTail (Fin.snoc gs g) j.castSucc = gs j.succ := by
      change Fin.snoc (α := fun _ : Fin (n + 2) => GHatOutcome params) gs g
        (j.succ.castSucc) = gs j.succ
      rw [Fin.snoc_castSucc]
    have hR :
        Fin.snoc (α := fun _ : Fin (n + 1) => GHatOutcome params)
          (gHatTupleOutcomeTail gs) g j.castSucc = gs j.succ := by
      rw [Fin.snoc_castSucc]
      rfl
    exact hL.trans hR.symm

/-- Ordered half-products satisfy a snoc recursion. -/
lemma fromHToG_gHatHalfProductOutcomeOperator_snoc
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ (n : ℕ) (xs : PointTuple params n) (x : Fq params)
      (gs : GHatTupleOutcome params n) (g : GHatOutcome params),
      gHatHalfProductOutcomeOperator params family (n + 1) (Fin.snoc xs x) (Fin.snoc gs g) =
        gHatHalfProductOutcomeOperator params family n xs gs *
          (gHatIdxMeas params family x).outcome g
  | 0, xs, x, gs, g => by
    have h0x : Fin.snoc (α := fun _ : Fin 1 => Fq params) xs x 0 = x := by
      simpa using (Fin.snoc_last (α := fun _ : Fin 1 => Fq params) x xs)
    have h0g : Fin.snoc (α := fun _ : Fin 1 => GHatOutcome params) gs g 0 = g := by
      simpa using (Fin.snoc_last (α := fun _ : Fin 1 => GHatOutcome params) g gs)
    simp [gHatHalfProductOutcomeOperator, h0x, h0g]
  | n + 1, xs, x, gs, g => by
      rw [gHatHalfProductOutcomeOperator]
      rw [fromHToG_pointTupleTail_snoc params xs x, fromHToG_gHatTupleOutcomeTail_snoc params gs g]
      rw [fromHToG_gHatHalfProductOutcomeOperator_snoc params family n
        (pointTupleTail xs) x (gHatTupleOutcomeTail gs) g]
      have hheadx : Fin.snoc (α := fun _ : Fin (n + 2) => Fq params) xs x 0 = xs 0 := by
        simp
      have hheadg : Fin.snoc (α := fun _ : Fin (n + 2) => GHatOutcome params) gs g 0 = gs 0 := by
        simp
      simp [hheadx, hheadg, gHatHalfProductOutcomeOperator, mul_assoc]

/-- Reversing a tuple turns the ordered half-product into its adjoint. -/
lemma fromHToG_gHatHalfProduct_reverse_eq_adjoint
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ (n : ℕ) (xs : PointTuple params n) (gs : GHatTupleOutcome params n),
      gHatHalfProductOutcomeOperator params family n
          ((fromHToGPointTupleReverseEquiv params n) xs)
          ((fromHToGGHatTupleOutcomeReverseEquiv params n) gs) =
        (gHatHalfProductOutcomeOperator params family n xs gs)ᴴ
  | 0, _xs, _gs => by
      simp [gHatHalfProductOutcomeOperator]
  | n + 1, xs, gs => by
      refine Fin.snocCases ?_ xs
      intro xs x
      refine Fin.snocCases ?_ gs
      intro gs g
      have hheadx : ((fromHToGPointTupleReverseEquiv params (n + 1)) (Fin.snoc xs x)) 0 = x := by
        change Fin.snoc (α := fun _ : Fin (n + 1) => Fq params) xs x
          (Fin.rev 0) = x
        rw [Fin.rev_zero]
        simp
      have hheadg :
          ((fromHToGGHatTupleOutcomeReverseEquiv params (n + 1)) (Fin.snoc gs g)) 0 = g := by
        change Fin.snoc (α := fun _ : Fin (n + 1) => GHatOutcome params) gs g
          (Fin.rev 0) = g
        rw [Fin.rev_zero]
        simp
      have htailx :
          pointTupleTail ((fromHToGPointTupleReverseEquiv params (n + 1)) (Fin.snoc xs x)) =
            (fromHToGPointTupleReverseEquiv params n) xs := by
        funext i
        change Fin.snoc (α := fun _ : Fin (n + 1) => Fq params) xs x
          (i.succ.rev) = xs i.rev
        rw [Fin.rev_succ]
        simp
      have htailg :
          gHatTupleOutcomeTail ((fromHToGGHatTupleOutcomeReverseEquiv params (n + 1))
            (Fin.snoc gs g)) =
              (fromHToGGHatTupleOutcomeReverseEquiv params n) gs := by
        funext i
        change Fin.snoc (α := fun _ : Fin (n + 1) => GHatOutcome params) gs g
          (i.succ.rev) = gs i.rev
        rw [Fin.rev_succ]
        simp
      rw [gHatHalfProductOutcomeOperator, hheadx, hheadg, htailx, htailg]
      rw [fromHToG_gHatHalfProduct_reverse_eq_adjoint params family n xs gs]
      rw [fromHToG_gHatHalfProductOutcomeOperator_snoc params family n xs x gs g]
      rw [Matrix.conjTranspose_mul, fromHToG_gHatIdxMeas_outcome_isHermitian]

end MIPStarRE.LDT.Pasting
