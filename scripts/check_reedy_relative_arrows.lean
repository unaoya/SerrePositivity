import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.RelativeArrow
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.WeakFactorizationSystem
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
  (r : ReedyStructure inverse direct α) {C : Type u'} [Category.{v'} C]

example (j : J) [HasColimitsOfShape (LatchingIndex r j) C] [HasPushouts C] :
    Arrow (J ⥤ C) ⥤ Arrow C := relativeLatchingArrow r j

example (j : J) [HasLimitsOfShape (MatchingIndex r j) C] [HasPullbacks C] :
    Arrow (J ⥤ C) ⥤ Arrow C := relativeMatchingArrow r j

example (j : J) [HasColimitsOfShape (LatchingIndex r j) C] [HasPushouts C]
    (W : MorphismProperty C) [W.RespectsIso] {F G F' G' : J ⥤ C}
    {τ : F ⟶ G} {σ : F' ⟶ G'} (e : Arrow.mk τ ≅ Arrow.mk σ) :
    W (relativeLatchingMap r j τ) ↔ W (relativeLatchingMap r j σ) :=
  relativeLatching_iso_iff r W e j

example [ModelCategory C] : (reedyLeft simplex (cofibrations C)).IsStableUnderRetracts :=
  inferInstance

example [ModelCategory C] : (reedyRight simplexOp (fibrations C)).IsStableUnderRetracts :=
  inferInstance

example (j : J) : BoundaryDiagram.toAdjoinFunctor r j C ⋙
    BoundaryDiagram.fromAdjoinFunctor r j C ≅ 𝟭 _ := BoundaryDiagram.reconstructionIso r j C

example (j : J) (hinj : Function.Injective r.deg) :
    BoundaryDiagram.degreeFunctor r j C hinj ⋙ BoundaryDiagram.fromUpperFunctor r j C ≅ 𝟭 _ :=
  BoundaryDiagram.degreeReconstructionIso r j C hinj

section Step
variable (j : J) (hinj : Function.Injective r.deg)
  [HasColimitsOfShape (LatchingIndex r j) C] [HasLimitsOfShape (MatchingIndex r j) C]
  [HasPushouts C] [HasPullbacks C] {F G : J ⥤ C} (τ : F ⟶ G)
  {lowerLeft lowerRight : MorphismProperty (Lower r (r.deg j) ⥤ C)}
  (a : MorphismProperty.MapFactorizationData lowerLeft lowerRight
    (Functor.whiskerLeft (lowerInclusion r (r.deg j)) τ))
  {left right : MorphismProperty C}
  (q : MorphismProperty.MapFactorizationData left right
    (RelativeExtension.map (BoundaryExtension.mapOfNatTrans r j τ) a))

-- Membership is proved after the actual ordinary-degree extension and its
-- reconstruction, not assumed for an unrelated boundary map.
example [left.RespectsIso] : left (((BoundaryDiagram.relativeLatchingArrow r j C).obj
    (Arrow.mk ((BoundaryDiagram.fromUpperFunctor r j C).map
      (DegreeFactorizationStep.leftMap r j hinj τ a q)))).hom) :=
  DegreeFactorizationStep.leftBoundary_mem r j hinj τ a q

example [right.RespectsIso] : right (((BoundaryDiagram.relativeMatchingArrow r j C).obj
    (Arrow.mk ((BoundaryDiagram.fromUpperFunctor r j C).map
      (DegreeFactorizationStep.rightMap r j hinj τ a q)))).hom) :=
  DegreeFactorizationStep.rightBoundary_mem r j hinj τ a q
end Step

-- The final factors now carry the actual relative Reedy classes; no ⊤ output
-- and no assumed degreewise intermediate diagrams are used in these consumers.
example [ModelCategory C] {F G : SimplexCategory ⥤ C} (τ : F ⟶ G) :
    MorphismProperty.MapFactorizationData
      (reedyLeft simplex (cofibrations C)) (reedyRight simplex (trivialFibrations C)) τ :=
  FactorizationSequence.reedyOfHasFactorization simplex τ
    (fun _ _ h ↦ SimplexCategory.ext h) (fun n ↦ ⟨SimplexCategory.mk n, rfl⟩)

example [ModelCategory C] {F G : SimplexCategoryᵒᵖ ⥤ C} (τ : F ⟶ G) :
    MorphismProperty.MapFactorizationData
      (reedyLeft simplexOp (trivialCofibrations C)) (reedyRight simplexOp (fibrations C)) τ :=
  FactorizationSequence.reedyOfHasFactorization simplexOp τ
    (fun _ _ h ↦ Opposite.unop_injective (SimplexCategory.ext h))
    (fun n ↦ ⟨Opposite.op (SimplexCategory.mk n), rfl⟩)

example [ModelCategory C] : MorphismProperty.IsWeakFactorizationSystem
    (reedyLeft simplex (cofibrations C)) (reedyRight simplex (trivialFibrations C)) :=
  weakFactorizationSystem simplex (cofibrations C) (trivialFibrations C)
    (fun _ _ h ↦ SimplexCategory.ext h) (fun n ↦ ⟨SimplexCategory.mk n, rfl⟩)

example [ModelCategory C] : MorphismProperty.IsWeakFactorizationSystem
    (reedyLeft simplex (trivialCofibrations C)) (reedyRight simplex (fibrations C)) :=
  weakFactorizationSystem simplex (trivialCofibrations C) (fibrations C)
    (fun _ _ h ↦ SimplexCategory.ext h) (fun n ↦ ⟨SimplexCategory.mk n, rfl⟩)

example [ModelCategory C] : MorphismProperty.IsWeakFactorizationSystem
    (reedyLeft simplexOp (cofibrations C)) (reedyRight simplexOp (trivialFibrations C)) :=
  weakFactorizationSystem simplexOp (cofibrations C) (trivialFibrations C)
    (fun _ _ h ↦ Opposite.unop_injective (SimplexCategory.ext h))
    (fun n ↦ ⟨Opposite.op (SimplexCategory.mk n), rfl⟩)

example [ModelCategory C] : MorphismProperty.IsWeakFactorizationSystem
    (reedyLeft simplexOp (trivialCofibrations C)) (reedyRight simplexOp (fibrations C)) :=
  weakFactorizationSystem simplexOp (trivialCofibrations C) (fibrations C)
    (fun _ _ h ↦ Opposite.unop_injective (SimplexCategory.ext h))
    (fun n ↦ ⟨Opposite.op (SimplexCategory.mk n), rfl⟩)

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.CategoryTheory.RelativeArrow,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.RelativeArrow,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryDiagram,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryDiagramIso,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryReconstruction,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryDegree,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FactorizationArrowComparison,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FactorizationRestrictionArrow,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FactorizationClasses,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.WeakFactorizationSystem]
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
  logInfo m!"Reedy relative-arrow audit passed: {count} declarations in {seen.size} modules."
