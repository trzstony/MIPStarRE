import Lean
import MIPStarRE.LDT.Test.MainTheorem.MainFormal

/-!
# Axiom audits for the low individual degree test

Regression checks that the final theorem `mainFormal`, its sampling-parameter
corollary `mainFormalWithK`, and the principal steps of the simplified proof
depend only on the standard Lean axioms `propext`, `Classical.choice`, and
`Quot.sound`.  In particular none of them depends on `sorryAx`.

The audited steps follow the proof in `blueprint/src/low_degree_simplified.tex`:
the state-dependent orthogonalization lemma and its consequence for consistent
measurements, the one-measurement Naimark dilation, the canonical semidefinite
program certificate, self-improvement with dilation, commutativity of the point
and slice measurements, pasting, the main induction, and the role-register
reduction from general to symmetric strategies.

This module is built explicitly in CI rather than imported from the umbrella
library modules, so the axiom audits stay out of normal downstream imports
while still acting as regression tests.
-/

open Lean Elab Command

private def resolveDeclIdent (id : TSyntax `ident) : CommandElabM Name := do
  liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo id

elab "assert_standard_axioms " id:ident : command => do
  let declName ← resolveDeclIdent id
  let axioms := (← Lean.collectAxioms declName).qsort Name.lt
  let expected := #[``propext, ``Classical.choice, ``Quot.sound].qsort Name.lt
  unless axioms == expected do
    throwError
      m!"'{declName}' depends on axioms {axioms.toList}, expected exactly " ++
        m!"{expected.toList}"

assert_standard_axioms MIPStarRE.LDT.Test.mainFormal
assert_standard_axioms MIPStarRE.LDT.Test.mainFormalWithK
assert_standard_axioms MIPStarRE.LDT.MainInductionStep.simplifiedMainInduction
assert_standard_axioms MIPStarRE.LDT.MainInductionStep.simplifiedAnswerMainInduction
assert_standard_axioms MIPStarRE.LDT.MainInductionStep.answerLdPastingSimplified
assert_standard_axioms MIPStarRE.LDT.SelfImprovement.selfImprovementWithDilation
assert_standard_axioms MIPStarRE.LDT.SelfImprovement.self_improvement_helper_with_contraction
assert_standard_axioms MIPStarRE.LDT.SelfImprovement.matrixSdpCanonicalStrongDuality
assert_standard_axioms MIPStarRE.LDT.CommutativityPoints.answerCommutativityPoints
assert_standard_axioms MIPStarRE.LDT.Commutativity.comMain_of_commutativityPoints
assert_standard_axioms MIPStarRE.LDT.ExpansionHypercubeGraph.localToGlobal
assert_standard_axioms MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimark

section Orthogonalization

open MIPStarRE.LDT.MakingMeasurementsProjective

assert_standard_axioms SimplifiedOrthogonalization.exists_projective_measurement_linear_bound
assert_standard_axioms SimplifiedOrthogonalization.consistent_measurement_linear_bound
assert_standard_axioms SimplifiedOrthogonalization.right_consistent_measurement_linear_bound

end Orthogonalization

assert_standard_axioms MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_is_good_three_mul
assert_standard_axioms MIPStarRE.LDT.ProjStrat.simplifiedRoleRegisterPointConsistency
assert_standard_axioms
  MIPStarRE.LDT.ProjStrat.sourceRoleRegisterFullPolynomialSelfConsistency_ofPointConsistency
assert_standard_axioms MIPStarRE.LDT.Preliminaries.polynomialCollisionMass_le_mdq
