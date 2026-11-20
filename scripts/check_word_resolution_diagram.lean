import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarWordResolution

universe u v w u' v' w'
noncomputable section
open CategoryTheory
open SerrePositivity SerrePositivity.SimplicialModel

section General
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {M : Type w} [MonoidWithZero M] {N : Type w'} [MonoidWithZero N]
example (F : C ⥤ D) (h : M →*₀ N) :
    RetractWords.map F h ⋙ RetractWords.augmentation D N =
      RetractWords.augmentation C M ⋙ F := RetractWords.map_augmentation F h
example (F : C ⥤ D) (h : M →*₀ N) :
    RetractWords.sourceFunctor C M ⋙ RetractWords.map F h =
      F ⋙ RetractWords.sourceFunctor D N := RetractWords.source_map F h
example : Cat.{v, u} ⥤ Cat.{max u v w, u} := WordPresentationCat.functor M
example : SimplicialObject (Cat.{v, u} ⥤ Cat.{max u v w, u}) :=
  WordPresentationCat.simplicial
example (A : SimplicialObject Cat.{v, u}) :
    SimplicialObject (SimplicialObject Cat.{max u v w, u}) := WordPresentationCat.bisimplicial A
example (A : SimplicialObject Cat.{max u v w, u}) :
    WordPresentationAugmentation.diagonal.{u, max u v w, w} A ⟶ A :=
  WordPresentationAugmentation.diagonalAugmentation.{u, v, w} A
example (A : SimplicialObject Cat.{max u v w, u}) :
    WordPresentationSection.diagonalSection.{u, v, w} A ≫
      WordPresentationAugmentation.diagonalAugmentation.{u, v, w} A = 𝟙 A :=
  WordPresentationSection.diagonalSection_augmentation A
end General

section Actual
open HomotopyFunctionComplex.OrdinaryBarWordResolution
variable (C : Type u) [Category.{v} C]
example : SimplicialObject (SimplicialObject Cat.{max u v, u}) := bisimplicial C
example : SimplicialObject Cat.{max u v, u} := diagonal C
example (n : SimplexCategoryᵒᵖ) : (diagonal C).obj n ⥤ Cᵒᵖ × C := projection C n
example {n m k l : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (φ : k ⟶ l) :
    ((bisimplicial C).map θ).app k ≫ ((bisimplicial C).obj m).map φ =
      ((bisimplicial C).obj n).map φ ≫ ((bisimplicial C).map θ).app l :=
  mixed_naturality C θ φ
example {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    ((diagonal C).map θ).toFunctor ⋙ projection C m = projection C n :=
  projection_naturality C θ
example : fromFreeResolution C ≫ toFreeResolution C = 𝟙 (source C) := fromFree_toFree C
example : fromFreeResolution C ≫ augmentation C = sourceAugmentation C := fromFree_augmentation C
end Actual

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.WordPresentationCat,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.WordPresentationAugmentation,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.WordPresentationSection,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarWordResolution]
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
  unless modules.size == expected.size do throwError "Missing word resolution diagram modules"
  logInfo m!"Word resolution diagram audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
