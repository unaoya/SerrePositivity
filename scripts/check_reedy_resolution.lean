import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexResolution
import Lean.Util.CollectAxioms

noncomputable section
universe v u
open CategoryTheory HomotopicalAlgebra SerrePositivity.Reedy
variable {C : Type u} [Category.{v} C] [ModelCategory C]

-- Ordinary existence needs no source functorial factorization.
example (X : C) : CofibrantResolution simplex X := cosimplicialResolution X
example (X : C) : FibrantResolution simplexOp X := simplicialResolution X

example (X : C) (n : SimplexCategory) :
    weakEquivalences C ((cosimplicialResolution X).augmentation.app n) :=
  (cosimplicialResolution X).augmentation_weakEquivalence n

example (X : C) (n : SimplexCategoryᵒᵖ) :
    weakEquivalences C ((simplicialResolution X).coaugmentation.app n) :=
  (simplicialResolution X).coaugmentation_weakEquivalence n

example (X : C) (n : SimplexCategory) : IsCofibrant ((cosimplicialResolution X).obj.obj n) :=
  (cosimplicialResolution X).isCofibrant_obj n

example (X : C) (n : SimplexCategoryᵒᵖ) : IsFibrant ((simplicialResolution X).obj.obj n) :=
  (simplicialResolution X).isFibrant_obj n

example (X : C) {n m : SimplexCategory} (f : n ⟶ m) :
    weakEquivalences C ((cosimplicialResolution X).obj.map f) :=
  (cosimplicialResolution X).homotopicallyConstant f

example (X : C) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    weakEquivalences C ((simplicialResolution X).obj.map f) :=
  (simplicialResolution X).homotopicallyConstant f

-- The entire functor and comparison are constructed from source data.
example (source : MorphismProperty.FunctorialFactorizationData
    (cofibrations C) (trivialFibrations C)) :
    CofibrantResolutionFamily (C := C) simplex := cosimplicialResolutionFamily source

example (source : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations C) (fibrations C)) :
    FibrantResolutionFamily (C := C) simplexOp := simplicialResolutionFamily source

example (source : MorphismProperty.FunctorialFactorizationData
    (cofibrations C) (trivialFibrations C)) {X Y : C} (f : X ⟶ Y)
    (hf : weakEquivalences C f) (n : SimplexCategory) :
    weakEquivalences C (((cosimplicialResolutionFamily source).obj.map f).app n) :=
  (cosimplicialResolutionFamily source).map_weakEquivalence f hf n

example (source : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations C) (fibrations C)) {X Y : C} (f : X ⟶ Y)
    (hf : weakEquivalences C f) (n : SimplexCategoryᵒᵖ) :
    weakEquivalences C (((simplicialResolutionFamily source).obj.map f).app n) :=
  (simplicialResolutionFamily source).map_weakEquivalence f hf n

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ComponentClasses,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Resolution,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FunctorialResolution,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexResolution]
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
  logInfo m!"Reedy resolution audit passed: {count} declarations in {seen.size} modules."
