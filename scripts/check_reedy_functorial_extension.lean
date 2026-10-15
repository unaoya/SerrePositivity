import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FunctorialExtension
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FunctorFactorizationFamily
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryDegree
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexFinite
import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Lean.Util.CollectAxioms

universe v u t v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J) {C : Type u'} [Category.{v'} C]
  [HasColimitsOfShape (LatchingIndex r j) C] [HasLimitsOfShape (MatchingIndex r j) C]
  [HasPushouts C] [HasPullbacks C] {left right : MorphismProperty C}
  (data : MorphismProperty.FunctorialFactorizationData left right)

example : FactorizationProblem r j C ⥤ Arrow C :=
  FactorizationProblem.relativeBoundaryFunctor r j C

example : FactorizationProblem.leftTransformation r j C data ≫
    FactorizationProblem.rightTransformation r j C data =
      FactorizationProblem.originalTransformation r j C := FactorizationProblem.left_right data

example (a : FactorizationProblem r j C) :
    left (((BoundaryDiagram.relativeLatchingArrow r j C).obj
      (Arrow.mk ((FactorizationProblem.leftTransformation r j C data).app a))).hom) :=
  FactorizationProblem.leftTransformation_mem data a

example (a : FactorizationProblem r j C) :
    right (((BoundaryDiagram.relativeMatchingArrow r j C).obj
      (Arrow.mk ((FactorizationProblem.rightTransformation r j C data).app a))).hom) :=
  FactorizationProblem.rightTransformation_mem data a

-- The lower middle diagrams and their square maps are supplied by the source
-- factorization functor, not assumed as a compatible family in the test.
example : Arrow (J ⥤ C) ⥤ BoundaryDiagram r j C :=
  FunctorFactorAt.problemFunctor r j (FunctorFactorAt.ofSourceData r (r.deg j) data) ⋙
    FactorizationProblem.extensionFunctor r j C data

example [ModelCategory C] (j : SimplexCategory)
    (source : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    Arrow (SimplexCategory ⥤ C) ⥤ (Upper simplex (simplex.deg j) ⥤ C) :=
  FunctorFactorAt.problemFunctor simplex j
      (FunctorFactorAt.ofSourceData simplex (simplex.deg j) source) ⋙
    FactorizationProblem.extensionFunctor simplex j C source ⋙
    BoundaryDiagram.degreeFunctor simplex j C (fun _ _ h ↦ SimplexCategory.ext h)

example [ModelCategory C] (j : SimplexCategoryᵒᵖ)
    (source : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C)) :
    Arrow (SimplexCategoryᵒᵖ ⥤ C) ⥤ (Upper simplexOp (simplexOp.deg j) ⥤ C) :=
  FunctorFactorAt.problemFunctor simplexOp j
      (FunctorFactorAt.ofSourceData simplexOp (simplexOp.deg j) source) ⋙
    FactorizationProblem.extensionFunctor simplexOp j C source ⋙
    BoundaryDiagram.degreeFunctor simplexOp j C
      (fun _ _ h ↦ Opposite.unop_injective (SimplexCategory.ext h))

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FactorizationProblem,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.RelativeBoundaryFunctor,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FunctorialExtension,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FunctorFactorizationFamily]
  let mut count : Nat := 0
  let mut seen : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  for mod in expected do
    unless seen.contains mod do throwError "Module not audited: {mod}"
  logInfo m!"Reedy functorial-extension audit passed: {count} declarations in {seen.size} modules."
