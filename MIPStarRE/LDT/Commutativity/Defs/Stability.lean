import MIPStarRE.LDT.Commutativity.Defs.Core

/-!
# Section 11 commutativity: evaluated product families

The evaluated-slice product families `G^x_[g(u)=a] G^y_[h(v)=b]`, obtained from
the full-slice products by postprocessing both polynomial outcomes with point
evaluation.

## References

- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.Quantum
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (params : Parameters) [FieldModel params.q]

/-- Postprocess the full-slice ordered product at sampled points.
On the bipartite space `d * d`. -/
noncomputable def evaluatedFromFullSliceProductLeft (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxOpFamily (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    OpFamily.postprocess (fullSliceProductLeft params strategy family xy)
      (evaluateFullSliceOutcomeAtQuestion params q)

/-- Postprocess the full-slice reversed product at sampled points.
On the bipartite space `d * d`. -/
noncomputable def evaluatedFromFullSliceProductRight (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxOpFamily (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    OpFamily.postprocess (fullSliceProductRight params strategy family xy)
      (evaluateFullSliceOutcomeAtQuestion params q)

end MIPStarRE.LDT.Commutativity
