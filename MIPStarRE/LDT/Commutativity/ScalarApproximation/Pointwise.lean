import MIPStarRE.LDT.Commutativity.ScalarApproximation.Core
import MIPStarRE.LDT.CommutativityPoints.Approximation
import MIPStarRE.LDT.Preliminaries.SelfConsistency.Extensions

/-!
# Section 11 commutativity: pointwise scalar approximation

Pointwise overlap terms `⟨ψ, (I - G^x) ⊗ G^x ψ⟩` controlling both sides of
the `G`-stability estimate, used as the base for the averaged scalar bound.

## References

- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The slice self-consistency defect of `G` is at most `zeta / 2`. -/
lemma gCommStability_sliceSSC
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    BipartiteSSCRel strategy.state
      (uniformDistribution (Fq params))
      G
      (zeta / 2) := by
  constructor
  calc
    bipartiteSSCError strategy.state
        (uniformDistribution (Fq params))
        G
      = (1 / 2 : Error) *
          sddError strategy.state
            (uniformDistribution (Fq params))
            (IdxSubMeas.liftLeft G)
            (IdxSubMeas.liftRight G) := by
            unfold bipartiteSSCError sddError
            rw [avgOver_congr (uniformDistribution (Fq params))
              (fun x => qBipartiteSSCDefect strategy.state (G x))
              (fun x =>
                (1 / 2 : Error) *
                  qSDD strategy.state
                    ((G x).liftLeft)
                    ((G x).liftRight))]
            · rw [avgOver_const_mul]
              rfl
            · intro x
              simpa [hG x] using
                qBipartiteSSCDefect_eq_half_qSDD_of_proj
                  strategy.state strategy.permInvState (family.meas x)
    _ ≤ (1 / 2 : Error) * zeta := by
          have hsdd_bound :
              sddError strategy.state
                (uniformDistribution (Fq params))
                (IdxSubMeas.liftLeft G)
                (IdxSubMeas.liftRight G) ≤ zeta := by
            calc
              sddError strategy.state
                  (uniformDistribution (Fq params))
                  (IdxSubMeas.liftLeft G)
                  (IdxSubMeas.liftRight G)
                = sddError strategy.state
                    (uniformDistribution (Fq params))
                    (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas))
                    (IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) := by
                      unfold sddError
                      apply avgOver_congr
                      intro x
                      simp [IdxSubMeas.liftLeft, IdxSubMeas.liftRight,
                        IdxProjSubMeas.toIdxSubMeas, hG x]
              _ ≤ zeta := hself.sliceSelfConsistency.squaredDistanceBound
          have hhalf_nonneg : 0 ≤ (1 / 2 : Error) := by norm_num
          exact mul_le_mul_of_nonneg_left
            hsdd_bound
            hhalf_nonneg
    _ = zeta / 2 := by ring

/-- Slice strong self-consistency transfers to the evaluated point family.

The paper invokes the slice self-consistency item after postprocessing a slice
measurement by the predicate `g(truncatePoint u) = a`.  This lemma makes that
implicit data-processing step explicit: projectivity converts the left/right SDD
hypothesis into bipartite strong self-consistency with loss `1/2`,
question-dependent postprocessing converts it back to left/right SDD with the
compensating factor `2`, and uniform reindexing
`Point params.next ≃ Point params × Fq params` averages the height coordinate. -/
lemma evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft params family)
      (evaluatedPointFamilyRight params family)
      zeta := by
  have hsliceSSC :
      BipartiteSSCRel strategy.state
        (uniformDistribution (Fq params))
        (IdxProjSubMeas.toIdxSubMeas family.meas)
        (zeta / 2) := by
    change BipartiteSSCRel strategy.state
      (uniformDistribution (Fq params))
      (fun x => (family.meas x).toSubMeas) (zeta / 2)
    exact gCommStability_sliceSSC params strategy zeta family
      (fun x => (family.meas x).toSubMeas) (fun _ => rfl) hself
  have hpost :
      ∀ u : Point params,
        SDDRel strategy.state
          (uniformDistribution (Fq params))
          (IdxSubMeas.liftLeft
            (fun x => evaluateAt params u ((family.meas x).toSubMeas)))
          (IdxSubMeas.liftRight
            (fun x => evaluateAt params u ((family.meas x).toSubMeas)))
          zeta := by
    intro u
    have htmp :=
      Preliminaries.twoNotionsOfSelfConsistencyAfterEvaluation
        strategy.state
        strategy.permInvState
        (uniformDistribution (Fq params))
        (IdxProjSubMeas.toIdxSubMeas family.meas)
        (zeta / 2)
        (fun (_ : Fq params) (g : Polynomial params) => g u)
        hsliceSSC
    refine ⟨?_⟩
    have hbound :
        sddError strategy.state
          (uniformDistribution (Fq params))
          (IdxSubMeas.liftLeft
            (fun x => evaluateAt params u ((family.meas x).toSubMeas)))
          (IdxSubMeas.liftRight
            (fun x => evaluateAt params u ((family.meas x).toSubMeas))) ≤
        2 * (zeta / 2) := by
      simpa [evaluateAt, IdxProjSubMeas.toIdxSubMeas] using htmp.squaredDistanceBound
    calc
      sddError strategy.state
          (uniformDistribution (Fq params))
          (IdxSubMeas.liftLeft
            (fun x => evaluateAt params u ((family.meas x).toSubMeas)))
          (IdxSubMeas.liftRight
            (fun x => evaluateAt params u ((family.meas x).toSubMeas)))
        ≤ 2 * (zeta / 2) := hbound
      _ = zeta := by ring
  constructor
  let e := CommutativityPoints.pointNextEquiv params
  let f : Point params → Fq params → Error :=
    fun u x =>
      qSDD strategy.state
        (leftPlacedSubMeas (ιB := ι)
          (evaluateAt params u ((family.meas x).toSubMeas)))
        (rightPlacedSubMeas (ιA := ι)
          (evaluateAt params u ((family.meas x).toSubMeas)))
  rw [sddError]
  calc
    avgOver (uniformDistribution (Point params.next))
        (fun w =>
          qSDD strategy.state
            (evaluatedPointFamilyLeft params family w)
            (evaluatedPointFamilyRight params family w))
      = avgOver (uniformDistribution (Point params × Fq params))
          (fun ux => f ux.1 ux.2) := by
          calc
            avgOver (uniformDistribution (Point params.next))
                (fun w =>
                  qSDD strategy.state
                    (evaluatedPointFamilyLeft params family w)
                    (evaluatedPointFamilyRight params family w))
              = avgOver (uniformDistribution (Point params × Fq params))
                  (fun ux =>
                    qSDD strategy.state
                      (evaluatedPointFamilyLeft params family (e.symm ux))
                      (evaluatedPointFamilyRight params family (e.symm ux))) :=
                  avgOver_uniform_equiv e
                    (fun w =>
                      qSDD strategy.state
                        (evaluatedPointFamilyLeft params family w)
                        (evaluatedPointFamilyRight params family w))
            _ = avgOver (uniformDistribution (Point params × Fq params))
                  (fun ux => f ux.1 ux.2) := by
                    apply avgOver_congr
                    intro ux
                    rcases ux with ⟨u, x⟩
                    change qSDD strategy.state
                      (evaluatedPointFamilyLeft params family (appendPoint params u x))
                      (evaluatedPointFamilyRight params family (appendPoint params u x)) =
                        qSDD strategy.state
                          (leftPlacedSubMeas (ιB := ι)
                            (evaluateAt params u ((family.meas x).toSubMeas)))
                          (rightPlacedSubMeas (ιA := ι)
                            (evaluateAt params u ((family.meas x).toSubMeas)))
                    simp [evaluatedPointFamilyLeft, evaluatedPointFamilyRight,
                      evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint,
                      evaluateAt, truncatePoint_appendPoint, pointHeight_appendPoint]
    _ = avgOver (uniformDistribution (Point params))
          (fun u => avgOver (uniformDistribution (Fq params)) (fun x => f u x)) := by
            exact MIPStarRE.LDT.avgOver_uniform_prod f
    _ ≤ zeta := by
          exact avgOver_uniform_le_const
            (fun u : Point params =>
              avgOver (uniformDistribution (Fq params)) (fun x => f u x))
            zeta
            (fun u => (hpost u).squaredDistanceBound)

end MIPStarRE.LDT.Commutativity
