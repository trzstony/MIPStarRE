import MIPStarRE.LDT.Commutativity.Scaffold.Symmetry

/-!
# Section 11 commutativity: product estimates

Basic product-style lemmas on projective submeasurement outcomes — in
particular orthogonality of distinct outcomes — reused throughout the
Section 11 commutativity argument.

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

/-- Postprocessing a projective submeasurement preserves outcome projectivity. -/
lemma postprocess_proj_outcome
    {α β : Type*} [Fintype α] [Fintype β]
    (P : ProjSubMeas α ι) (f : α → β) (b : β) :
    (postprocess P.toSubMeas f).outcome b * (postprocess P.toSubMeas f).outcome b =
      (postprocess P.toSubMeas f).outcome b := by
  simpa using ProjSubMeas.postprocess_outcome_proj P f b

/-- Evaluating a projective polynomial family at a point preserves outcome projectivity. -/
lemma evaluatedPointFamily_outcome_proj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (u : Point params.next) (a : Fq params) :
    (evaluatedPointFamily params family u).outcome a *
        (evaluatedPointFamily params family u).outcome a =
      (evaluatedPointFamily params family u).outcome a := by
  simpa [evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint, evaluateAt] using
    postprocess_proj_outcome (family.meas (pointHeight params u))
      (fun g => g (truncatePoint params u)) a

/-- The positive square root of a submeasurement outcome squares back to that
outcome. -/
lemma sqrt_subMeas_outcome_mul_self
    {α : Type*} [Fintype α]
    (A : SubMeas α ι) (a : α) :
    CFC.sqrt (A.outcome a) * CFC.sqrt (A.outcome a) = A.outcome a := by
  simpa using CFC.sqrt_mul_sqrt_self (A.outcome a) (A.outcome_pos a)

/-- The `BAB` term in the evaluated-slice commutator expansion. -/
noncomputable def evaluatedSliceBABTerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) (ab : EvaluatedSliceOutcome params) : Error :=
  let A := (evaluatedPointFamily params family q.1).outcome ab.1
  let B := (evaluatedPointFamily params family q.2).outcome ab.2
  ev strategy.state <| leftTensor (ι₂ := ι) (B * A * B)

/-- The `ABA` term in the evaluated-slice commutator expansion. -/
noncomputable def evaluatedSliceABATerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) (ab : EvaluatedSliceOutcome params) : Error :=
  let A := (evaluatedPointFamily params family q.1).outcome ab.1
  let B := (evaluatedPointFamily params family q.2).outcome ab.2
  ev strategy.state <| leftTensor (ι₂ := ι) (A * B * A)

/-- The `BABA` term in the evaluated-slice commutator expansion. -/
noncomputable def evaluatedSliceBABATerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) (ab : EvaluatedSliceOutcome params) : Error :=
  let A := (evaluatedPointFamily params family q.1).outcome ab.1
  let B := (evaluatedPointFamily params family q.2).outcome ab.2
  ev strategy.state <| leftTensor (ι₂ := ι) (B * A * B * A)

/-- The `ABAB` term in the evaluated-slice commutator expansion. -/
noncomputable def evaluatedSliceABABTerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) (ab : EvaluatedSliceOutcome params) : Error :=
  let A := (evaluatedPointFamily params family q.1).outcome ab.1
  let B := (evaluatedPointFamily params family q.2).outcome ab.2
  ev strategy.state <| leftTensor (ι₂ := ι) (A * B * A * B)

/-- The first evaluated-slice factor viewed as a projective family. -/
noncomputable def evaluatedSliceFirstProj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxProjSubMeas (EvaluatedSliceQuestion params) (Fq params) ι :=
  fun q =>
    { toSubMeas := evaluatedSliceFirstFactor params family q
      proj := evaluatedPointFamily_outcome_proj params family q.1 }

/-- The second evaluated-slice factor viewed as a projective family. -/
noncomputable def evaluatedSliceSecondProj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxProjSubMeas (EvaluatedSliceQuestion params) (Fq params) ι :=
  fun q =>
    { toSubMeas := evaluatedSliceSecondFactor params family q
      proj := evaluatedPointFamily_outcome_proj params family q.2 }

/-- The first full-slice factor viewed as a projective family. -/
noncomputable def fullSliceFirstProj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxProjSubMeas (FullSliceQuestion params) (Polynomial params) ι :=
  fun q => family.meas q.1

/-- The second full-slice factor viewed as a projective family. -/
noncomputable def fullSliceSecondProj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxProjSubMeas (FullSliceQuestion params) (Polynomial params) ι :=
  fun q => family.meas q.2

/-- The `BAB` term in the full-slice commutator expansion. -/
noncomputable def fullSliceBABTerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : FullSliceQuestion params) (gh : FullSliceOutcome params) : Error :=
  let A := (fullSliceFirstFactor params family q).outcome gh.1
  let B := (fullSliceSecondFactor params family q).outcome gh.2
  ev strategy.state <| leftTensor (ι₂ := ι) (B * A * B)

/-- The `ABA` term in the full-slice commutator expansion. -/
noncomputable def fullSliceABATerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : FullSliceQuestion params) (gh : FullSliceOutcome params) : Error :=
  let A := (fullSliceFirstFactor params family q).outcome gh.1
  let B := (fullSliceSecondFactor params family q).outcome gh.2
  ev strategy.state <| leftTensor (ι₂ := ι) (A * B * A)

/-- The `BABA` term in the full-slice commutator expansion. -/
noncomputable def fullSliceBABATerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : FullSliceQuestion params) (gh : FullSliceOutcome params) : Error :=
  let A := (fullSliceFirstFactor params family q).outcome gh.1
  let B := (fullSliceSecondFactor params family q).outcome gh.2
  ev strategy.state <| leftTensor (ι₂ := ι) (B * A * B * A)

/-- The `ABAB` term in the full-slice commutator expansion. -/
noncomputable def fullSliceABABTerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : FullSliceQuestion params) (gh : FullSliceOutcome params) : Error :=
  let A := (fullSliceFirstFactor params family q).outcome gh.1
  let B := (fullSliceSecondFactor params family q).outcome gh.2
  ev strategy.state <| leftTensor (ι₂ := ι) (A * B * A * B)

end MIPStarRE.LDT.Commutativity
