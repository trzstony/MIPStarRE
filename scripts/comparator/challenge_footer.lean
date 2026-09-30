
namespace MIPStarRE.LDT
namespace Test

-- source: MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean:34-66  (MIPStarRE.LDT.Test.mainFormal)
/-- Simplified statement of `thm:main-formal`.

The strategy and the three projective-measurement conclusions are those of the
original theorem.  The simplified proof chooses the pasting length internally
and gives the error `21000 K_{m,d} (ε^(1/64) + (d/q)^(1/64))`.

**Local fix:** This bound follows `blueprint/src/low_degree_simplified.tex`,
`thm:main-formal`, which replaces the sampling parameter `k` of
`references/ldt-paper/test_definition.tex:180-202`.  The original statement is
recovered as the corollary `mainFormalWithK`. -/
theorem mainFormal
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.lowIndividualDegreeFailureProbability ≤ eps) :
    ∃ G_A : ProjMeas (Polynomial params) ιA,
      ∃ G_B : ProjMeas (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas)
            (simplifiedMainFormalError params eps) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (simplifiedMainFormalError params eps) ∧
          ConsRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily G_A.toSubMeas)
            (constSubMeasFamily G_B.toSubMeas)
            (simplifiedMainFormalError params eps) := by
  sorry

end Test
end MIPStarRE.LDT
