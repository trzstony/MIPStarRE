import MIPStarRE.LDT.Basic.AxisParallelLine

/-!
# Diagonal lines for the low individual degree test

Diagonal-line geometry and rebasing operations.

## References

- `references/ldt-paper/test_definition.tex`
- `blueprint/src/chapter/ch02_test.tex`
-/

namespace MIPStarRE.LDT

/-- A genuinely affine diagonal line in `F_q^m`. -/
structure DiagonalLine (params : Parameters) where
  base : Point params
  direction : Point params

deriving instance DecidableEq, Inhabited for DiagonalLine

namespace DiagonalLine

/-- The canonical affine parameterization `t ↦ base + t · direction`. -/
def pointAt {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) : Fq params → Point params :=
  fun t => addPoint ℓ.base (smulPoint t ℓ.direction)

/-- Rebase a diagonal line so that the old point `ℓ.pointAt t` becomes the new base point. -/
def rebaseAt {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) (t : Fq params) : DiagonalLine params where
  base := ℓ.pointAt t
  direction := ℓ.direction

theorem rebaseAt_pointAt {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) (t s : Fq params) :
    (rebaseAt ℓ t).pointAt s = ℓ.pointAt (addCoord t s) := by
  ext i
  simp only [pointAt, addPoint, addCoord, rebaseAt, smulPoint, mulCoord, decode_encodeScalar]
  rw [← encode_decodeScalar (ℓ.base i)]
  congr 1
  ring_nf

@[simp] theorem rebaseAt_zero {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) :
    rebaseAt ℓ zeroCoord = ℓ := by
  cases ℓ with
  | mk base direction =>
      change
        ({ base :=
             ({ base := base, direction := direction } : DiagonalLine params).pointAt zeroCoord,
           direction := direction } : DiagonalLine params) =
        ({ base := base, direction := direction } : DiagonalLine params)
      congr
      funext i
      simp [pointAt, addPoint, smulPoint, addCoord, mulCoord, zeroCoord]

theorem rebaseAt_rebase {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) (t s : Fq params) :
    rebaseAt (rebaseAt ℓ t) s = rebaseAt ℓ (addCoord t s) := by
  cases ℓ with
  | mk base direction =>
      change
        ({ base :=
             (rebaseAt
               ({ base := base, direction := direction } : DiagonalLine params) t).pointAt s,
           direction := direction } : DiagonalLine params) =
        ({ base :=
             ({ base := base, direction := direction } : DiagonalLine params).pointAt
               (addCoord t s),
           direction := direction } : DiagonalLine params)
      exact congrArg
        (fun b => ({ base := b, direction := direction } : DiagonalLine params))
        (rebaseAt_pointAt { base := base, direction := direction } t s)

/-- Embed a diagonal line into the slice at height `x`, keeping the new coordinate fixed. -/
def appendAtHeight (params : Parameters) [FieldModel params.q]
    (ℓ : DiagonalLine params) (x : Fq params) : DiagonalLine params.next where
  base := appendPoint params ℓ.base x
  direction := appendPoint params ℓ.direction zeroCoord

@[simp] theorem appendAtHeight_rebaseAt {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) (t x : Fq params) :
    appendAtHeight params (rebaseAt ℓ t) x =
      rebaseAt (appendAtHeight params ℓ x) t := by
  cases ℓ with
  | mk base direction =>
      change
        ({ base := appendPoint params (addPoint base (smulPoint t direction)) x,
           direction := appendPoint params direction zeroCoord } : DiagonalLine params.next) =
        ({ base := addPoint (appendPoint params base x)
             (smulPoint t (appendPoint params direction zeroCoord)),
           direction := appendPoint params direction zeroCoord } : DiagonalLine params.next)
      congr
      funext i
      by_cases hi : i.1 < params.m
      · simp only [appendPoint, addPoint, smulPoint, addCoord, mulCoord, hi, ↓reduceDIte]
        rfl
      · simp only [appendPoint, hi, ↓reduceDIte, addPoint, addCoord, smulPoint, mulCoord,
          zeroCoord, decode_encodeScalar]
        rw [← encode_decodeScalar x]
        congr 1
        calc
          decodeScalar x = decodeScalar x + decodeScalar t * (0 : Scalar params) := by ring
          _ = decodeScalar (encodeScalar (decodeScalar x)) +
                decodeScalar t * decodeScalar (encodeScalar 0) := by
              rw [show decodeScalar (encodeScalar (decodeScalar x)) = decodeScalar x from
                  decode_encodeScalar (decodeScalar x),
                show decodeScalar (encodeScalar (0 : Scalar params)) = (0 : Scalar params) from
                  decode_encodeScalar (0 : Scalar params)]

end DiagonalLine

end MIPStarRE.LDT
