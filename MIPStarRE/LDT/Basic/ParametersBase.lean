import Mathlib

/-!
# Basic parameters and scalar infrastructure for the low individual degree test

Core parameter data, finite-field models, and coordinate arithmetic.

Note: this module contributes declarations to the comparator statement closure
of `mainFormal`, which must elaborate in the same environment as the
Mathlib-only `Challenge.lean`.  Keep the full `import Mathlib`; do not narrow
it.  See `docs/comparator.md`, "Environment alignment".
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

abbrev Error := ℝ

inductive Role where
  | A
  | B
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Parameters for the `(m,q,d)` low individual degree test.

Besides the usual positivity assumptions, we bundle the paper-faithful witness
that `q = p^n` is a prime power. -/
structure Parameters where
  m : ℕ
  q : ℕ
  d : ℕ
  hm : 0 < m
  /-- Kept as a compatibility field so existing positivity proofs can continue
  to use `params.hq`; it is derivable from `hqPrimePower`. -/
  hq : 0 < q
  /-- Paper-faithful witness that `q` is a prime power. -/
  hqPrimePower : ∃ p n, Nat.Prime p ∧ 0 < n ∧ q = p ^ n

namespace Parameters

/-- Positivity of the field-size parameter after casting to the repository's
real-valued error scalar type. -/
theorem q_cast_pos (params : Parameters) : 0 < (params.q : Error) :=
  Nat.cast_pos.mpr params.hq

end Parameters

/-- The successor test obtained by appending one coordinate. -/
def Parameters.next (params : Parameters) : Parameters :=
  { m := params.m + 1
    q := params.q
    d := params.d
    hm := Nat.succ_pos _
    hq := params.hq
    hqPrimePower := params.hqPrimePower }

namespace Parameters

/-- The predecessor parameters obtained by removing the last coordinate from a
non-base ambient dimension.

This is the inverse construction to `Parameters.next` on the data fields.  The
proof fields are inherited from the original parameter bundle, so the inverse is
propositional rather than definitional. -/
def previous (params : Parameters) (hm : 1 < params.m) : Parameters :=
  { m := params.m - 1
    q := params.q
    d := params.d
    hm := Nat.sub_pos_of_lt hm
    hq := params.hq
    hqPrimePower := params.hqPrimePower }

/-- Removing the last coordinate and then applying `Parameters.next` recovers the
original non-base parameters. -/
theorem previous_next_eq (params : Parameters) (hm : 1 < params.m) :
    (previous params hm).next = params := by
  cases params with
  | mk m q d hm0 hq hqPrimePower =>
      have hsub : m - 1 + 1 = m := Nat.sub_add_cancel (le_of_lt hm)
      simp [previous, Parameters.next, hsub]

/-- A bundled predecessor for a parameter set known to be a successor dimension. -/
structure SuccessorDecomposition (params : Parameters) where
  /-- The predecessor parameter bundle. -/
  pred : Parameters
  /-- The predecessor's successor is the original parameter bundle. -/
  next_eq : pred.next = params

/-- Every parameter bundle of dimension strictly larger than one has a bundled
predecessor whose successor is propositionally equal to the original bundle. -/
def successorDecompositionOfOneLtM (params : Parameters) (hm : 1 < params.m) :
    SuccessorDecomposition params where
  pred := previous params hm
  next_eq := previous_next_eq params hm

/-- A positive dimension that is not the base dimension is strictly larger than
one. -/
theorem one_lt_m_of_ne_one (params : Parameters) (hm_ne_one : params.m ≠ 1) :
    1 < params.m :=
  lt_of_le_of_ne params.hm (Ne.symm hm_ne_one)

/-- Non-base parameters have a bundled predecessor decomposition. -/
def successorDecompositionOfNeOne (params : Parameters) (hm_ne_one : params.m ≠ 1) :
    SuccessorDecomposition params :=
  successorDecompositionOfOneLtM params (one_lt_m_of_ne_one params hm_ne_one)

end Parameters

instance {params : Parameters} : NeZero params.q :=
  ⟨Nat.ne_of_gt params.hq⟩

abbrev Fq (params : Parameters) := Fin params.q
abbrev Point (params : Parameters) := Fin params.m → Fq params
abbrev PointTuple (params : Parameters) (k : ℕ) := Fin k → Fq params

instance {params : Parameters} : Inhabited (Fin params.m) :=
  ⟨⟨0, params.hm⟩⟩

instance {params : Parameters} : Inhabited (Fq params) :=
  ⟨⟨0, params.hq⟩⟩

/-- A bundled field model for the paper's `F_q`, together with a coding equivalence
to the repository's finite carrier `Fin q`. -/
class FieldModel (q : ℕ) where
  K : Type*
  instField : Field K
  instFintype : Fintype K
  instDecidableEq : DecidableEq K
  equiv : K ≃ Fin q

attribute [instance_reducible, instance] FieldModel.instField FieldModel.instFintype
  FieldModel.instDecidableEq

namespace FieldModel

/-- The carrier bundled in a `FieldModel q` has exactly `q` elements, matching the
paper's finite-field convention `|F_q| = q` (`preliminaries.tex`, lines 17--19). -/
@[simp] theorem card (q : ℕ) [FieldModel q] :
    Fintype.card (FieldModel.K q) = q := by
  simpa using Fintype.card_congr (FieldModel.equiv (q := q))

end FieldModel

/-- Reuse an already chosen field model for successor parameters. Since Lean
prefers larger numeric priorities, this transport uses `200` so it is tried
before the canonical fallback above. -/
instance (priority := 200) {params : Parameters} [inst : FieldModel params.q] :
    FieldModel params.next.q := by
  simpa [Parameters.next] using inst

abbrev Scalar (params : Parameters) [FieldModel params.q] := FieldModel.K params.q
abbrev PolynomialModel (params : Parameters) [FieldModel params.q] :=
  MvPolynomial (Fin params.m) (Scalar params)
abbrev LinePolynomialModel (params : Parameters) [FieldModel params.q] :=
  _root_.Polynomial (Scalar params)

/-- The chosen scalar model for the paper's `F_q` has exactly `q` elements
(`preliminaries.tex`, lines 17--19 and 89--93). -/
@[simp] theorem scalar_card (params : Parameters) [FieldModel params.q] :
    Fintype.card (Scalar params) = params.q := by
  simp [Scalar]

/-- Interpret a coded coordinate in `Fin q` as a scalar in the chosen field model. -/
def decodeScalar {params : Parameters} [FieldModel params.q] (x : Fq params) : Scalar params :=
  (FieldModel.equiv (q := params.q)).symm x

/-- Re-encode a field-model scalar as its canonical representative in `Fin q`. -/
def encodeScalar {params : Parameters} [FieldModel params.q] (x : Scalar params) : Fq params :=
  FieldModel.equiv (q := params.q) x

@[simp] theorem encode_decodeScalar {params : Parameters} [FieldModel params.q] (x : Fq params) :
    encodeScalar (decodeScalar x) = x := by
  simp [encodeScalar, decodeScalar]

@[simp] theorem decode_encodeScalar {params : Parameters} [FieldModel params.q]
    (x : Scalar params) :
    decodeScalar (encodeScalar x) = x := by
  simp [encodeScalar, decodeScalar]

/-- The zero coordinate. -/
def zeroCoord {params : Parameters} [FieldModel params.q] : Fq params :=
  encodeScalar 0

/-- Coordinate addition transported through the `Fin q` coding. -/
def addCoord {params : Parameters} [FieldModel params.q] (x y : Fq params) : Fq params :=
  encodeScalar (decodeScalar x + decodeScalar y)

/-- Coordinate subtraction transported through the `Fin q` coding. -/
def subCoord {params : Parameters} [FieldModel params.q] (x y : Fq params) : Fq params :=
  encodeScalar (decodeScalar x - decodeScalar y)

@[simp] theorem addCoord_subCoord_right {params : Parameters} [FieldModel params.q]
    (x y : Fq params) :
    addCoord y (subCoord x y) = x := by
  unfold addCoord subCoord
  rw [decode_encodeScalar]
  simp [sub_eq_add_neg]

@[simp] theorem addCoord_subCoord_left {params : Parameters} [FieldModel params.q]
    (x y : Fq params) :
    addCoord (subCoord x y) y = x := by
  unfold addCoord subCoord
  rw [decode_encodeScalar]
  simp [sub_eq_add_neg]

@[simp] theorem subCoord_addCoord_right {params : Parameters} [FieldModel params.q]
    (x y : Fq params) :
    subCoord (addCoord x y) y = x := by
  unfold subCoord addCoord
  rw [decode_encodeScalar]
  simp [sub_eq_add_neg]

/-- Coordinate multiplication transported through the `Fin q` coding. -/
def mulCoord {params : Parameters} [FieldModel params.q] (x y : Fq params) : Fq params :=
  encodeScalar (decodeScalar x * decodeScalar y)

/-- Pointwise addition in the coded ambient space. -/
def addPoint {params : Parameters} [FieldModel params.q] (u v : Point params) : Point params :=
  fun i => addCoord (u i) (v i)

/-- Scalar multiplication in the coded ambient space. -/
def smulPoint {params : Parameters} [FieldModel params.q] (t : Fq params) (u : Point params) :
    Point params :=
  fun i => mulCoord t (u i)

/-- The zero point in `F_q^m`. -/
def zeroPoint {params : Parameters} [FieldModel params.q] : Point params :=
  fun _ => zeroCoord

/-- The inclusion of the first `m` coordinates into `m + 1` coordinates. -/
def embedCoord (params : Parameters) : Fin params.m → Fin params.next.m :=
  fun i => ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self params.m)⟩

/-- The old-coordinate inclusion into the appended coordinate space is injective. -/
theorem embedCoord_injective (params : Parameters) :
    Function.Injective (embedCoord params) := by
  intro i j hij
  apply Fin.ext
  simpa [embedCoord] using congrArg Fin.val hij

/-- The last coordinate of `F_q^(m+1)`. -/
def lastCoord (params : Parameters) : Fin params.next.m :=
  ⟨params.m, Nat.lt_succ_self params.m⟩

/-- No old coordinate is the appended last coordinate. -/
theorem embedCoord_ne_lastCoord (params : Parameters) (i : Fin params.m) :
    embedCoord params i ≠ lastCoord params := by
  intro h
  have hval := congrArg Fin.val h
  simp [embedCoord, lastCoord] at hval
  omega

/-- Append a final coordinate to a point in `F_q^m`. -/
def appendPoint (params : Parameters) (u : Point params) (x : Fq params) : Point params.next :=
  fun i => if h : i.1 < params.m then u ⟨i.1, h⟩ else x

/-- Truncate the last coordinate of a point in `F_q^{m+1}`. -/
def truncatePoint (params : Parameters) (u : Point params.next) : Point params :=
  fun i => u ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self params.m)⟩

/-- Extract the final coordinate of a point in `F_q^{m+1}`. -/
def pointHeight (params : Parameters) (u : Point params.next) : Fq params :=
  u (lastCoord params)

@[simp] theorem truncatePoint_appendPoint (params : Parameters)
    (u : Point params) (x : Fq params) :
    truncatePoint params (appendPoint params u x) = u := by
  funext i
  simp [truncatePoint, appendPoint, i.2]

@[simp] theorem pointHeight_appendPoint (params : Parameters)
    (u : Point params) (x : Fq params) :
    pointHeight params (appendPoint params u x) = x := by
  simp [pointHeight, lastCoord, appendPoint]

/-- Decode a coded point as a tuple of scalars in the chosen field model. -/
def decodePoint {params : Parameters} [FieldModel params.q] (u : Point params) :
    Fin params.m → Scalar params :=
  fun i => decodeScalar (u i)

/-- Evaluate a multivariate polynomial over the chosen field model on a coded point. -/
noncomputable def evalPolynomialModel (params : Parameters) [FieldModel params.q]
    (p : PolynomialModel params) (u : Point params) : Fq params :=
  encodeScalar (MvPolynomial.eval (decodePoint u) p)

/-- Evaluate a univariate polynomial over the chosen field model on a coded point. -/
noncomputable def evalLinePolynomialModel (params : Parameters) [FieldModel params.q]
    (p : LinePolynomialModel params) (t : Fq params) : Fq params :=
  encodeScalar (_root_.Polynomial.eval (decodeScalar t) p)

end MIPStarRE.LDT
