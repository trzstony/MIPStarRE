import MIPStarRE.LDT.Basic.DistributionMapAverages
import MIPStarRE.LDT.CommutativityPoints.SharedHelpers.Core

/-!
# Section 10 commutativity points: shared-line helpers

Compatibility lemmas between sampled point pairs and shared-diagonal line
questions, used by both the lift and drop comparisons.

## References

- `references/ldt-paper/commutativity-points.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Matrix MatrixOrder ComplexOrder BigOperators
private theorem sharedDiagonalLineQuestionOfPointPair_sampledPointPair
    (params : Parameters)
    [FieldModel params.q]
    (s : PointPairQuestion params × Fq params) :
    sampledPointPairFromSharedDiagonalQuestion params
      (sharedDiagonalLineQuestionOfPointPair params s) = s.1 := by
  rcases s with ⟨⟨u, v⟩, t⟩
  refine Prod.ext ?_ ?_
  · funext i
    simp [sampledPointPairFromSharedDiagonalQuestion, sharedDiagonalLineQuestionOfPointPair,
      DiagonalLine.pointAt, addPoint, smulPoint, addCoord, subCoord, mulCoord]
  · funext i
    suffices h :
        encodeScalar
            (decodeScalar (u i) - decodeScalar t * (decodeScalar (v i) - decodeScalar (u i)) +
              (decodeScalar t + 1) * (decodeScalar (v i) - decodeScalar (u i))) =
          v i by
      simpa [sampledPointPairFromSharedDiagonalQuestion, sharedDiagonalLineQuestionOfPointPair,
        DiagonalLine.pointAt, addPoint, smulPoint, addCoord, subCoord, mulCoord] using h
    rw [← encode_decodeScalar (v i)]
    congr 1
    ring_nf
    simp

private theorem sharedDiagonalLineQuestionOfPointPair_of_line
    (params : Parameters)
    [FieldModel params.q]
    (ℓ : DiagonalLine params)
    (t : Fq params) :
    sharedDiagonalLineQuestionOfPointPair params
      (((ℓ.pointAt t, ℓ.pointAt (addCoord t (encodeScalar 1))), t)) =
      (ℓ, (t, addCoord t (encodeScalar 1))) := by
  cases ℓ with
  | mk base direction =>
      change
        (({ base := fun i => _, direction := fun i => _ } : DiagonalLine params),
          (t, addCoord t (encodeScalar 1))) =
        ({ base := base, direction := direction }, (t, addCoord t (encodeScalar 1)))
      congr
      · funext i
        suffices h :
            encodeScalar
                (decodeScalar (base i) + decodeScalar t * decodeScalar (direction i) -
                  decodeScalar t *
                    ((decodeScalar t + 1) * decodeScalar (direction i) -
                      decodeScalar t * decodeScalar (direction i))) =
              base i by
          simpa [DiagonalLine.pointAt, addPoint, smulPoint, addCoord, subCoord,
            mulCoord] using h
        rw [← encode_decodeScalar (base i)]
        congr 1
        ring_nf
        simp
      · funext i
        suffices h :
            encodeScalar
                ((decodeScalar t + 1) * decodeScalar (direction i) -
                  decodeScalar t * decodeScalar (direction i)) =
              direction i by
          simpa [DiagonalLine.pointAt, addPoint, smulPoint, addCoord, subCoord,
            mulCoord] using h
        rw [← encode_decodeScalar (direction i)]
        congr 1
        ring_nf
        simp

private noncomputable def pointPairSharedDiagonalLine_ignore_first_equiv
    (params : Parameters)
    [FieldModel params.q] :
    (PointPairQuestion params × Fq params) ≃ PointDiagonalLineQuestion params where
  toFun := fun s =>
    let q := sharedDiagonalLineQuestionOfPointPair params s
    (q.1, q.2.2)
  invFun := fun r =>
    let ℓ := r.1
    let tv := r.2
    (((ℓ.pointAt (subCoord tv (encodeScalar 1)), ℓ.pointAt tv)),
      subCoord tv (encodeScalar 1))
  left_inv := fun ⟨⟨u, v⟩, t⟩ => by
    refine Prod.ext ?_ ?_
    · simpa [Prod.ext_iff, sampledPointPairFromSharedDiagonalQuestion,
        sharedDiagonalLineQuestionOfPointPair, addCoord, subCoord] using
        sharedDiagonalLineQuestionOfPointPair_sampledPointPair params ((u, v), t)
    · simp [sharedDiagonalLineQuestionOfPointPair, addCoord, subCoord]
  right_inv := fun ⟨ℓ, tv⟩ => by
    simpa [addCoord, subCoord] using
      congrArg (fun q => (q.1, q.2.2))
        (sharedDiagonalLineQuestionOfPointPair_of_line params ℓ
          (subCoord tv (encodeScalar 1)))

private noncomputable def pointPairSharedDiagonalLine_ignore_second_equiv
    (params : Parameters)
    [FieldModel params.q] :
    (PointPairQuestion params × Fq params) ≃ PointDiagonalLineQuestion params where
  toFun := fun s =>
    let q := sharedDiagonalLineQuestionOfPointPair params s
    (q.1, q.2.1)
  invFun := fun r =>
    let ℓ := r.1
    let t := r.2
    (((ℓ.pointAt t, ℓ.pointAt (addCoord t (encodeScalar 1))), t))
  left_inv := fun ⟨⟨u, v⟩, t⟩ => by
    refine Prod.ext ?_ ?_
    · simpa [Prod.ext_iff, sampledPointPairFromSharedDiagonalQuestion,
        sharedDiagonalLineQuestionOfPointPair] using
        sharedDiagonalLineQuestionOfPointPair_sampledPointPair params ((u, v), t)
    · simp [sharedDiagonalLineQuestionOfPointPair]
  right_inv := fun ⟨ℓ, t⟩ => by
    simpa using
      congrArg (fun q => (q.1, q.2.1))
        (sharedDiagonalLineQuestionOfPointPair_of_line params ℓ t)

lemma avgOver_pointPairSharedDiagonalLine_ignore_first
    (params : Parameters)
    [FieldModel params.q]
    (f : PointDiagonalLineQuestion params → Error) :
    avgOver (pointPairSharedDiagonalLineDistribution params)
      (fun q => f (q.1, q.2.2)) =
      avgOver (pointWithDiagonalLineDistribution params) f := by
  calc
    avgOver (pointPairSharedDiagonalLineDistribution params)
        (fun q => f (q.1, q.2.2))
      = avgOver (uniformDistribution (PointDiagonalLineQuestion params)) f := by
          simpa [pointPairSharedDiagonalLineDistribution] using
            (avgOver_uniform_map_eq_uniform_of_factor_equiv
              (m := sharedDiagonalLineQuestionOfPointPair params)
              (g := fun q : PointPairDiagonalLineQuestion params => (q.1, q.2.2))
              (e := pointPairSharedDiagonalLine_ignore_first_equiv params)
              (h := by
                intro s
                rfl)
              (f := f))
    _ = avgOver (pointWithDiagonalLineDistribution params) f := by
          simp [pointWithDiagonalLineDistribution]

lemma avgOver_pointPairSharedDiagonalLine_ignore_second
    (params : Parameters)
    [FieldModel params.q]
    (f : PointDiagonalLineQuestion params → Error) :
    avgOver (pointPairSharedDiagonalLineDistribution params)
      (fun q => f (q.1, q.2.1)) =
      avgOver (pointWithDiagonalLineDistribution params) f := by
  calc
    avgOver (pointPairSharedDiagonalLineDistribution params)
        (fun q => f (q.1, q.2.1))
      = avgOver (uniformDistribution (PointDiagonalLineQuestion params)) f := by
          simpa [pointPairSharedDiagonalLineDistribution] using
            (avgOver_uniform_map_eq_uniform_of_factor_equiv
              (m := sharedDiagonalLineQuestionOfPointPair params)
              (g := fun q : PointPairDiagonalLineQuestion params => (q.1, q.2.1))
              (e := pointPairSharedDiagonalLine_ignore_second_equiv params)
              (h := by
                intro s
                rfl)
              (f := f))
    _ = avgOver (pointWithDiagonalLineDistribution params) f := by
          simp [pointWithDiagonalLineDistribution]

lemma avgOver_pointPairSharedDiagonalLine_sampled_pair
    (params : Parameters)
    [FieldModel params.q]
    (f : PointPairQuestion params → Error) :
    avgOver (pointPairSharedDiagonalLineDistribution params)
      (fun q => f (sampledPointPairFromSharedDiagonalQuestion params q)) =
      avgOver (uniformDistribution (PointPairQuestion params)) f := by
  simpa [pointPairSharedDiagonalLineDistribution] using
    (avgOver_uniform_map_eq_uniform_fst_of_factor_equiv
      (m := sharedDiagonalLineQuestionOfPointPair params)
      (g := sampledPointPairFromSharedDiagonalQuestion params)
      (e := Equiv.refl (PointPairQuestion params × Fq params))
      (h := sharedDiagonalLineQuestionOfPointPair_sampledPointPair params)
      (f := f))

end MIPStarRE.LDT.CommutativityPoints
