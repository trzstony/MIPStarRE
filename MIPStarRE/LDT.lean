import MIPStarRE.LDT.Basic.ParametersBase
import MIPStarRE.LDT.Basic.SqrtBounds
import MIPStarRE.LDT.Basic.AxisParallelLine
import MIPStarRE.LDT.Basic.DiagonalLine
import MIPStarRE.LDT.Basic.LinePolynomials
import MIPStarRE.LDT.Basic.LowDegreePolynomial
import MIPStarRE.LDT.Basic.ParametersFiniteAnswers
import MIPStarRE.LDT.Basic.QuantumState
import MIPStarRE.LDT.Basic.OperatorExpectations
import MIPStarRE.LDT.Basic.Distribution
import MIPStarRE.LDT.Basic.PMFAverages
import MIPStarRE.LDT.Basic.PMFUniformAverages
import MIPStarRE.LDT.Basic.DistributionUniformSums
import MIPStarRE.LDT.Basic.DistributionAvg
import MIPStarRE.LDT.Basic.DistributionPMF
import MIPStarRE.LDT.Basic.DistributionProduct
import MIPStarRE.LDT.Basic.DistributionMapAverages
import MIPStarRE.LDT.Basic.DistributionUniform
import MIPStarRE.LDT.Basic.SubMeasurementCore
import MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPStarRE.LDT.Basic.OpFamily
import MIPStarRE.LDT.Test.Defs
import MIPStarRE.LDT.Test.StrategyBiProjUnsymmetrization
import MIPStarRE.LDT.Test.StrategyPolynomialFamilies
import MIPStarRE.LDT.Test.MainTheorem.MainFormal
import MIPStarRE.LDT.Preliminaries.Defs
import MIPStarRE.LDT.Preliminaries.ComparisonCore
import MIPStarRE.LDT.Preliminaries.DistanceBounds
import MIPStarRE.LDT.Preliminaries.ConsistencyBridges
import MIPStarRE.LDT.Preliminaries.ComparisonProjective
import MIPStarRE.LDT.Preliminaries.SwitchSandwichGapBounds.Left
import MIPStarRE.LDT.Preliminaries.SwitchSandwichGapBounds.Middle
import MIPStarRE.LDT.Preliminaries.SwitchSandwichMain.Completeness
import MIPStarRE.LDT.Preliminaries.BipartiteSelfConsistency.Completion
import MIPStarRE.LDT.Preliminaries.CompletionTransfer
import MIPStarRE.LDT.Preliminaries.Triangles.SimEq
import MIPStarRE.LDT.MakingMeasurementsProjective.Defs
import MIPStarRE.LDT.MakingMeasurementsProjective.Statements
import MIPStarRE.LDT.MakingMeasurementsProjective.Projectivization
import MIPStarRE.LDT.MakingMeasurementsProjective.NaimarkFull
import MIPStarRE.LDT.MakingMeasurementsProjective.MarginalStates
import MIPStarRE.LDT.ExpansionHypercubeGraph.Theorems.Results
import MIPStarRE.LDT.GlobalVariance.Defs.Families
import MIPStarRE.LDT.GlobalVariance.Theorems.MainTheorems
import MIPStarRE.LDT.SelfImprovement.Defs
import MIPStarRE.LDT.SelfImprovement.MatrixRealization.Canonical.Saturated
import MIPStarRE.LDT.SelfImprovement.MatrixRealization.Canonical.StrongDuality.Separation
import MIPStarRE.LDT.SelfImprovement.Theorems.AddInUFullStatement
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.SelfImprovementTop.Core
import MIPStarRE.LDT.CommutativityPoints.Defs
import MIPStarRE.LDT.CommutativityPoints.Approximation
import MIPStarRE.LDT.CommutativityPoints.SharedHelpers.SharedLine
import MIPStarRE.LDT.CommutativityPoints.AnswerTheorems
import MIPStarRE.LDT.Commutativity.Defs.Normalization
import MIPStarRE.LDT.Commutativity.Main.Results
import MIPStarRE.LDT.Pasting.Defs.Families
import MIPStarRE.LDT.Commutativity.Scaffold.Core
import MIPStarRE.LDT.MainInductionStep.Defs
import MIPStarRE.LDT.Pasting.Sandwich.PastedFamilies
import MIPStarRE.LDT.Pasting.Core.LdGbcon
import MIPStarRE.LDT.Pasting.Core.CompletePart
import MIPStarRE.LDT.Preliminaries.Polynomials
import MIPStarRE.LDT.Preliminaries.PolynomialAgreement

-- Mathlib 4.31 header checks require this for this aggregate module.
set_option linter.style.header false

/-!
# Low individual degree test

This root module provides the Lean development for the low individual degree test,
including the test definition, preliminary analytic estimates, the
projectivization theorem, the main-induction interface, global variance,
self-improvement, commutativity, and pasting.
-/
