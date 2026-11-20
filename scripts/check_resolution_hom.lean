import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ChosenResolutionHom
import Lean.Util.CollectAxioms

noncomputable section
universe v u
open CategoryTheory HomotopicalAlgebra SerrePositivity
open SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

example : Cᵒᵖ ⥤ C ⥤ SSet.{v} := chosenResolutionHom cof fib

example (X : Cᵒᵖ) (Y : C) (n : SimplexCategoryᵒᵖ) :
    (((chosenResolutionHom cof fib).obj X).obj Y).obj n =
      (((Reedy.cosimplicialResolutionFamily cof).obj.obj X.unop).obj n.unop ⟶
        (fibrantTarget fib).obj Y) := rfl

example (X : C) : IsFibrant ((fibrantTarget fib).obj X) := fibrantTarget_isFibrant fib X

example {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) :
    weakEquivalences C ((fibrantTarget fib).map f) :=
  fibrantTarget_map_weakEquivalence fib f hf

example {X X' : Cᵒᵖ} (f : X ⟶ X') (Y : C) (n : SimplexCategoryᵒᵖ)
    (h : ((Reedy.cosimplicialResolutionFamily cof).obj.obj X.unop).obj n.unop ⟶
      (fibrantTarget fib).obj Y) :
    ((((chosenResolutionHom cof fib).map f).app Y).app n) h =
      (((Reedy.cosimplicialResolutionFamily cof).obj.map f.unop).app n.unop) ≫ h :=
  resolutionHom_map_source _ _ f Y n h

example (X : Cᵒᵖ) {Y Y' : C} (f : Y ⟶ Y') (n : SimplexCategoryᵒᵖ)
    (h : ((Reedy.cosimplicialResolutionFamily cof).obj.obj X.unop).obj n.unop ⟶
      (fibrantTarget fib).obj Y) :
    ((((chosenResolutionHom cof fib).obj X).map f).app n) h = h ≫ (fibrantTarget fib).map f :=
  resolutionHom_map_target _ _ X f n h

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.ResolutionHom,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ChosenResolutionHom]
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
  logInfo m!"Resolution Hom audit passed: {count} declarations in {seen.size} modules."
