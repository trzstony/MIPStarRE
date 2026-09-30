import MIPStarRE.LDT.Pasting.ComparisonLemmas.LdSandwichLineOnePoint.EndpointEquivs
import MIPStarRE.LDT.Pasting.Core.LdGbcon

/-!
# Section 12 pasting: line one-point transport — endpoint lemmas

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

noncomputable def ldSandwichLineOnePointRightEndpointMeasurement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (ux : Point params × Fq params) : Measurement (Fq params) ι := by
  let ℓ : AxisParallelLine params.next :=
    { base := appendPoint params ux.1 zeroCoord
      direction := lastCoord params }
  exact postprocessMeasurement (strategy.axisParallelMeasurement ℓ).toMeasurement (fun f => f ux.2)

lemma ldSandwichLineOnePointRightEndpointMeasurement_toSubMeas
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (ux : Point params × Fq params) :
    (ldSandwichLineOnePointRightEndpointMeasurement params strategy ux).toSubMeas =
      postprocess (verticalLineMeasurementFamily params strategy ux.1) (fun f => f ux.2) := by
  simp [ldSandwichLineOnePointRightEndpointMeasurement, verticalLineMeasurementFamily,
    postprocessMeasurement]
  rfl

lemma ldSandwichLineOnePoint_endpoint_ldGbcon_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta zeta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    ConsRel strategy.state
      (uniformDistribution (Point params × Fq params))
      (fun ux => postprocess (evaluateAt params ux.1 ((family.meas ux.2).toSubMeas)) some)
      (fun ux =>
        postprocess
          (ldSandwichLineOnePointRightEndpointMeasurement params strategy ux).toSubMeas
          some)
        (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
  have hgb := ldGbcon_of_axis_self params strategy eps delta zeta haxis hself family hcons
  have hprod :
      ConsRel strategy.state
        (uniformDistribution (Point params × Fq params))
        (fun ux =>
          evaluateFiberFamilyAtNextPoint params (IdxProjSubMeas.toIdxSubMeas family.meas)
            ((pointNextEquiv params).symm ux))
        (fun ux =>
          postprocess
            (verticalLineMeasurementFamily params strategy
              (truncatePoint params ((pointNextEquiv params).symm ux)))
            (fun f => f (pointHeight params ((pointNextEquiv params).symm ux))))
        (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
    exact (Preliminaries.consRel_uniform_equiv
      (pointNextEquiv params)
      strategy.state
      (evaluateFiberFamilyAtNextPoint params (IdxProjSubMeas.toIdxSubMeas family.meas))
      (fun u =>
        postprocess
          (verticalLineMeasurementFamily params strategy (truncatePoint params u))
          (fun f => f (pointHeight params u)))
      (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta))).1 hgb
  have hprod' :
      ConsRel strategy.state
        (uniformDistribution (Point params × Fq params))
        (fun ux =>
          postprocess (evaluateAt params ux.1 ((family.meas ux.2).toSubMeas))
            (fun a => some a))
        (fun ux =>
          postprocess
            (postprocess (verticalLineMeasurementFamily params strategy ux.1) (fun f => f ux.2))
            (fun a => some a))
        (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
    have hproc :=
      Preliminaries.consRelDataProcessing_questionDependent
        strategy.state
        (uniformDistribution (Point params × Fq params))
        (fun ux =>
          evaluateFiberFamilyAtNextPoint params (IdxProjSubMeas.toIdxSubMeas family.meas)
            ((pointNextEquiv params).symm ux))
        (fun ux =>
          postprocess
            (verticalLineMeasurementFamily params strategy
              (truncatePoint params ((pointNextEquiv params).symm ux)))
            (fun f => f (pointHeight params ((pointNextEquiv params).symm ux))))
        (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta))
        (fun _ a => some a)
        hprod
    simpa [pointNextEquiv, evaluateFiberFamilyAtNextPoint, IdxProjSubMeas.toIdxSubMeas,
      postprocess_postprocess, Function.comp] using hproc
  convert hprod' using 2
  · rename_i ux
    rw [ldSandwichLineOnePointRightEndpointMeasurement_toSubMeas]
    rfl

-- The proof lifts the endpoint consistency relation through the split
-- sandwiched-line equivalence; the chain of rewriting identities unfolds this
-- equivalence and the endpoint-family definition.
lemma ldSandwichLineOnePoint_endpoint_ldGbcon_lift_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta zeta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (k i : ℕ) (hi : i < k) :
    ConsRel strategy.state
      (uniformDistribution (SandwichedLineQuestion params k))
      (fun q =>
        postprocess
          (evaluateAt params q.1 ((family.meas (q.2 ⟨i, hi⟩)).toSubMeas))
          some)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
  let iFin : Fin k := ⟨i, hi⟩
  let Rest := {j : Fin k // j ≠ iFin} → Fq params
  let e := sandwichedLineQuestionSplitAtEquiv params iFin
  let endpointLeft : IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) ι :=
    fun q =>
      postprocess
        (evaluateAt params q.1 ((family.meas (q.2 iFin)).toSubMeas))
        some
  let endpointRight : IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) ι :=
    ldSandwichLineOnePointRightFamily params strategy family k i
  have hbase := ldSandwichLineOnePoint_endpoint_ldGbcon_of_axis_self
    params strategy eps delta zeta haxis hself family hcons
  have hprod :
      ConsRel strategy.state
        (uniformDistribution ((Point params × Fq params) × Rest))
        (fun q =>
          postprocess
            (evaluateAt params q.1.1 ((family.meas q.1.2).toSubMeas))
            some)
        (fun q =>
          postprocess
            (ldSandwichLineOnePointRightEndpointMeasurement params strategy q.1).toSubMeas
            some)
        (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
    exact Preliminaries.consRel_uniform_prod_fst strategy.state
      (fun ux : Point params × Fq params =>
        postprocess (evaluateAt params ux.1 ((family.meas ux.2).toSubMeas)) some)
      (fun ux : Point params × Fq params =>
        postprocess
          (ldSandwichLineOnePointRightEndpointMeasurement params strategy ux).toSubMeas
          some)
      (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) hbase
  have hlift :=
    (Preliminaries.consRel_uniform_equiv e strategy.state endpointLeft endpointRight
      (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta))).2
      (by
        convert hprod using 2
        · simp [e, endpointLeft, iFin,
            sandwichedLineQuestionSplitAtEquiv]
        · simp only [ne_eq, sandwichedLineQuestionSplitAtEquiv, Equiv.coe_fn_symm_mk,
            ldSandwichLineOnePointRightFamily, hi, ↓reduceDIte, Equiv.funSplitAt_symm_apply,
            ldSandwichLineOnePointRightEndpointMeasurement_toSubMeas, endpointRight, iFin, e]
          exact (postprocess_postprocess _ _ _).symm)
  simpa [endpointLeft, endpointRight, iFin] using hlift

lemma gHatIdxMeas_outcome_some_eq_evaluateAt
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (x : Fq params) (u : Point params) (a : Fq params) :
    (∑ g : GHatOutcome params,
      if Option.map (fun g' : Polynomial params => g' u) g = some a then
        (gHatIdxMeas params family x).outcome g
      else
        0) =
      (evaluateAt params u ((family.meas x).toSubMeas)).outcome a := by
  rw [Fintype.sum_option]
  conv_lhs =>
    simp [gHatIdxMeas, completeSubMeas]
  conv_rhs =>
    simp [evaluateAt, postprocess, Finset.sum_filter]

lemma gHatSandwichFamily_restrict_zero_outcome_some
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {n : ℕ} (xs : PointTuple params (n + 1))
    (u : Point params) (a : Fq params) :
    (postprocess
      (restrictSubMeas (gHatSandwichFamily params family (n + 1) xs)
        (fun gs => (gs 0).isSome = true))
      (fun gs => Option.map (fun g : Polynomial params => g u) (gs 0))).outcome (some a) =
      ∑ gs : GHatTupleOutcome params (n + 1),
        if Option.map (fun g : Polynomial params => g u) (gs 0) = some a then
          let half := gHatHalfProductOutcomeOperator params family (n + 1) xs gs
          half * halfᴴ
        else
          0 := by
  conv_lhs =>
    simp [postprocess, restrictSubMeas, gHatSandwichFamily, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro gs _hgs
  by_cases hmap : Option.map (fun g : Polynomial params => g u) (gs 0) = some a
  · rcases Option.map_eq_some_iff.mp hmap with ⟨g, hgs0, hg⟩
    simp [hgs0]
  · have hnone : ¬ ∃ g : Polynomial params, gs 0 = some g ∧ g u = a := by
      rintro ⟨g, hgs0, hg⟩
      exact hmap (Option.map_eq_some_iff.mpr ⟨g, hgs0, hg⟩)
    simp [hnone]

lemma evaluateAt_postprocess_some_outcome_none_eq_zero
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (x : Fq params) (u : Point params) :
    (postprocess (evaluateAt params u ((family.meas x).toSubMeas)) some).outcome none = 0 := by
  simp [evaluateAt, postprocess]

lemma gHatSandwichFamily_restrict_zero_outcome_none_eq_zero
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {n : ℕ} (xs : PointTuple params (n + 1))
    (u : Point params) :
    (postprocess
      (restrictSubMeas (gHatSandwichFamily params family (n + 1) xs)
        (fun gs => (gs 0).isSome = true))
      (fun gs => Option.map (fun g : Polynomial params => g u) (gs 0))).outcome none = 0 := by
  conv_lhs =>
    simp [postprocess, restrictSubMeas, gHatSandwichFamily, Finset.sum_filter]
  apply Finset.sum_eq_zero
  intro gs _hgs
  by_cases hsome : (gs 0).isSome = true
  · rcases Option.isSome_iff_exists.mp hsome with ⟨g, hg⟩
    simp [hg]
  · simp [hsome]

lemma ldSandwichLineOnePointLeftFamily_zero_outcome_some_eq_endpoint
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (hk : 0 < k)
    (q : SandwichedLineQuestion params k) (a : Fq params) :
    ((ldSandwichLineOnePointLeftFamily params strategy family k 0) q).outcome (some a) =
      (evaluateAt params q.1 ((family.meas (q.2 ⟨0, hk⟩)).toSubMeas)).outcome a := by
  cases k with
  | zero => cases hk
  | succ r =>
      let xs : PointTuple params (r + 1) := q.2
      let u : Point params := q.1
      let G : GHatOutcome params → MIPStarRE.Quantum.Op ι := fun g =>
        (gHatIdxMeas params family (xs 0)).outcome g
      let T : GHatTupleOutcome params r → MIPStarRE.Quantum.Op ι := fun gs =>
        gHatHalfProductOutcomeOperator params family r (pointTupleTail xs) gs
      have hleft :
          ((ldSandwichLineOnePointLeftFamily params strategy family (r + 1) 0) q).outcome
              (some a) =
            ∑ gs : GHatTupleOutcome params (r + 1),
              if Option.map (fun g : Polynomial params => g u) (gs 0) = some a then
                let half := gHatHalfProductOutcomeOperator params family (r + 1) xs gs
                half * halfᴴ
              else
                0 := by
        simpa [ldSandwichLineOnePointLeftFamily, xs, u] using
          gHatSandwichFamily_restrict_zero_outcome_some params family xs u a
      have hsplit :
          (∑ gs : GHatTupleOutcome params (r + 1),
            if Option.map (fun g : Polynomial params => g u) (gs 0) = some a then
              let half := gHatHalfProductOutcomeOperator params family (r + 1) xs gs
              half * halfᴴ
            else
              0) =
            ∑ p : GHatOutcome params × GHatTupleOutcome params r,
              if Option.map (fun g : Polynomial params => g u) p.1 = some a then
                (G p.1 * T p.2) * (G p.1 * T p.2)ᴴ
              else
                0 := by
        exact Fintype.sum_equiv (gHatTupleOutcomeConsEquiv' params r)
          (fun gs : GHatTupleOutcome params (r + 1) =>
            if Option.map (fun g : Polynomial params => g u) (gs 0) = some a then
              let half := gHatHalfProductOutcomeOperator params family (r + 1) xs gs
              half * halfᴴ
            else
              0)
          (fun p : GHatOutcome params × GHatTupleOutcome params r =>
            if Option.map (fun g : Polynomial params => g u) p.1 = some a then
              (G p.1 * T p.2) * (G p.1 * T p.2)ᴴ
            else
              0)
          (by
            intro gs
            simp [gHatTupleOutcomeConsEquiv', gHatHalfProductOutcomeOperator, T, G])
      calc
        ((ldSandwichLineOnePointLeftFamily params strategy family (r + 1) 0) q).outcome
            (some a)
            = ∑ gs : GHatTupleOutcome params (r + 1),
              if Option.map (fun g : Polynomial params => g u) (gs 0) = some a then
                let half := gHatHalfProductOutcomeOperator params family (r + 1) xs gs
                half * halfᴴ
              else
                0 := hleft
        _ = ∑ p : GHatOutcome params × GHatTupleOutcome params r,
              if Option.map (fun g : Polynomial params => g u) p.1 = some a then
                (G p.1 * T p.2) * (G p.1 * T p.2)ᴴ
              else
                0 := hsplit
        _ = ∑ g : GHatOutcome params,
              ∑ gs : GHatTupleOutcome params r,
                if Option.map (fun g' : Polynomial params => g' u) g = some a then
                  (G g * T gs) * (G g * T gs)ᴴ
                else
                  0 := by
              rw [← Finset.univ_product_univ, Finset.sum_product]
        _ = ∑ g : GHatOutcome params,
              if Option.map (fun g' : Polynomial params => g' u) g = some a then
                G g
              else
                0 := by
              refine Finset.sum_congr rfl ?_
              intro g _hg
              by_cases hmap : Option.map (fun g' : Polynomial params => g' u) g = some a
              · have hherm : (G g)ᴴ = G g := by
                  simpa [G] using (gHatIdxMeas params family (xs 0)).outcome_hermitian g
                have hproj : G g * G g = G g := by
                  simpa [G] using gHatIdxMeas_proj params family (xs 0) g
                calc
                  (∑ gs : GHatTupleOutcome params r,
                    if Option.map (fun g' : Polynomial params => g' u) g = some a then
                      (G g * T gs) * (G g * T gs)ᴴ
                    else
                      0) = ∑ gs : GHatTupleOutcome params r,
                        G g * (T gs * (T gs)ᴴ) * G g := by
                        refine Finset.sum_congr rfl ?_
                        intro gs _hgs
                        simp [hmap, Matrix.conjTranspose_mul, hherm, mul_assoc]
                  _ = G g *
                        (∑ gs : GHatTupleOutcome params r, T gs * (T gs)ᴴ) * G g := by
                        rw [← Finset.sum_mul, ← Matrix.mul_sum]
                  _ = G g := by
                        have htail :
                            (∑ gs : GHatTupleOutcome params r, T gs * (T gs)ᴴ) = 1 := by
                          simpa [T, gHatSandwichFamily,
                            gHatHalfProductTotalOperator_eq_one] using
                            (gHatSandwichFamily params family r (pointTupleTail xs)).sum_eq_total
                        simp [htail, hproj]
                  _ = if Option.map (fun g' : Polynomial params => g' u) g = some a then
                        G g
                      else
                        0 := by
                        simp [hmap]
              · simp [hmap]
        _ = (evaluateAt params u ((family.meas (xs 0)).toSubMeas)).outcome a := by
              simpa [G] using
                gHatIdxMeas_outcome_some_eq_evaluateAt params family (xs 0) u a

lemma ldSandwichLineOnePointLeftFamily_zero_eq_endpoint
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (hk : 0 < k) :
    ldSandwichLineOnePointLeftFamily params strategy family k 0 =
      (fun q : SandwichedLineQuestion params k =>
        postprocess
          (evaluateAt params q.1 ((family.meas (q.2 ⟨0, hk⟩)).toSubMeas))
          some) := by
  funext q
  apply SubMeas.ext
  · intro o
    cases o with
    | none =>
        cases k with
        | zero => cases hk
        | succ r =>
            have hleftNone :
                ((ldSandwichLineOnePointLeftFamily params strategy family (r + 1) 0) q).outcome
                    none = 0 := by
              simpa [ldSandwichLineOnePointLeftFamily] using
                gHatSandwichFamily_restrict_zero_outcome_none_eq_zero params family q.2 q.1
            have hrightNone :
                (postprocess
                  (evaluateAt params q.1 ((family.meas (q.2 ⟨0, hk⟩)).toSubMeas))
                  some).outcome none = 0 := by
              exact
                evaluateAt_postprocess_some_outcome_none_eq_zero
                  params family (q.2 ⟨0, hk⟩) q.1
            rw [hleftNone, hrightNone]
    | some a =>
        simpa [postprocess, Finset.sum_filter] using
          ldSandwichLineOnePointLeftFamily_zero_outcome_some_eq_endpoint
            params strategy family hk q a
  · rw [← ((ldSandwichLineOnePointLeftFamily params strategy family k 0) q).sum_eq_total]
    rw [← (postprocess
      (evaluateAt params q.1 ((family.meas (q.2 ⟨0, hk⟩)).toSubMeas)) some).sum_eq_total]
    refine Finset.sum_congr rfl ?_
    intro o _
    cases o with
    | none =>
        cases k with
        | zero => cases hk
        | succ r =>
            have hleftNone :
                ((ldSandwichLineOnePointLeftFamily params strategy family (r + 1) 0) q).outcome
                    none = 0 := by
              simpa [ldSandwichLineOnePointLeftFamily] using
                gHatSandwichFamily_restrict_zero_outcome_none_eq_zero params family q.2 q.1
            have hrightNone :
                (postprocess
                  (evaluateAt params q.1 ((family.meas (q.2 ⟨0, hk⟩)).toSubMeas))
                  some).outcome none = 0 := by
              exact
                evaluateAt_postprocess_some_outcome_none_eq_zero
                  params family (q.2 ⟨0, hk⟩) q.1
            rw [hleftNone, hrightNone]
    | some a =>
        simpa [postprocess, Finset.sum_filter] using
          ldSandwichLineOnePointLeftFamily_zero_outcome_some_eq_endpoint
            params strategy family hk q a

end MIPStarRE.LDT.Pasting
