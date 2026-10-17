import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.SimplicialModel

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)
  (a : NerveFirstChoice.System (OrdinaryBarCenters.leftChoices R))
  (b : NerveFirstChoice.System (OrdinaryBarCenters.rightChoices R))

-- This is exactly the ordinary bar used by the original right comparison.
example : OrdinaryBarEvaluation.bar R = (OrdinaryResolutionBar.functor (C := C)).obj
    ((RightResolutionMapping.projection (C := C)).obj R) := rfl

-- Evaluation is an actual map in the auxiliary universe; no model there is an input.
example : OrdinaryBarEvaluation.bar R ⟶
    UniverseLift.obj.{u} (OrdinaryBarFirstAction.output R) :=
  OrdinaryBarEvaluation.evaluation R a b

example : OrdinaryBarReference.sectionMap R ≫ OrdinaryBarEvaluation.evaluation R a b =
    UniverseLift.map.{u} (OrdinaryBarReference.smallAction R a b) :=
  OrdinaryBarReference.section_evaluation R a b

-- Original labels are transported by the actual ordinary resolution arrow.
example (n : SimplexCategoryᵒᵖ) (c : (OrdinaryBarEvaluation.bar R).obj n) :
    ((OrdinaryResolutionPairs.raw (C := C)).map
      (OrdinaryBarSimplexCone.arrow R a b n c)).app n (c.obj 0).left.val =
        ((OrdinaryBarEvaluation.evaluation R a b).app n c).down :=
  OrdinaryBarSimplexCone.arrow_label R a b n c

example (n : SimplexCategoryᵒᵖ) (c : (OrdinaryBarEvaluation.bar R).obj n) :
    c.obj 0 ⟶ OrdinaryBarSimplexCone.element R a b n c :=
  OrdinaryBarSimplexCone.elementArrow R a b n c

-- A whole natural transformation inside the same comma category, including all simplex maps.
example : OrdinaryBarCommaCone.barIndices R ⋙ OrdinaryBarCommaCone.first R ⟶
    OrdinaryBarCommaCone.barIndices R ⋙ OrdinaryBarCommaCone.rows R :=
  OrdinaryBarCommaCone.barCone R a b

example (n : SimplexCategoryᵒᵖ) (c : (OrdinaryBarEvaluation.bar R).obj n) :
    ((OrdinaryBarCommaCone.cone R a b).app
      (op (SerrePositivity.NerveSimplexEndpoint.ofChain
        (OrdinaryBarEvaluation.chain R n c)))).left =
      OrdinaryBarSimplexCone.arrow R a b n c :=
  OrdinaryBarCommaCone.cone_recovery R a b n c

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

-- Existence of whole systems follows from the original small model, not extra choices axioms.
example : NerveFirstChoice.System (OrdinaryBarCenters.leftChoices R) :=
  OrdinaryBarCenters.leftSystem R hcof
example : NerveFirstChoice.System (OrdinaryBarCenters.rightChoices R) :=
  OrdinaryBarCenters.rightSystem R hcof

example : weakEquivalences SSet.{v} (OrdinaryBarReference.smallAction R a b) :=
  OrdinaryBarReference.smallAction_weakEquivalence R a b hcof hfib

example : IsIso (AnodyneHomotopy.anodyneQ.map
    (OrdinaryBarReference.sectionMap R ≫ OrdinaryBarEvaluation.evaluation R a b)) :=
  OrdinaryBarReference.section_evaluation_isIso R a b hcof hfib

example : IsIso (AnodyneHomotopy.anodyneQ.map
    ((OrdinaryResolutionBar.right (C := C)).app R)) ↔
    IsIso (AnodyneHomotopy.anodyneQ.map (OrdinaryBarEvaluation.evaluation R a b)) :=
  OrdinaryBarRightEvaluation.right_isIso_iff_evaluation R a b hcof hfib

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarCenters,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFirstAction,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarEvaluation,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarReference,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarSimplexCone,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarRowDiagram,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarCommaCone,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarRightEvaluation]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  unless modules.size == expected.size do throwError "Missing ordinary bar evaluation modules"
  logInfo m!"Ordinary bar evaluation audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
