import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarHomotopyDescent

universe v w uD vD u
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex

-- The class category has Hom in v; its large realization is fully faithful without a model.
example (X Y : SmallKanHomotopy.Object.{v}) : Type v := X ⟶ Y

example {D : Type uD} [Category.{vD} D] (L : SSet.{max w v} ⥤ D)
    [L.IsLocalization SSet.anodyneExtensions] :
    (SmallKanHomotopy.realization.{v, w} L).FullyFaithful :=
  SmallKanHomotopy.fullyFaithful L

section Base
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

-- This codomain explicitly uses homotopy-class arrows, not actual simplicial maps.
example : Cᵒᵖ × C ⥤ SmallKanHomotopy.Object.{v} :=
  OrdinaryBarHomotopyDescent.functor hcof hfib

example : OrdinaryBarHomotopyDescent.functor (C := C) hcof hfib ⋙
    OrdinaryBarHomotopyDescent.realization.{v, u} ≅
      OrdinaryResolutionBar.functor ⋙ AnodyneHomotopy.anodyneQ :=
  OrdinaryBarHomotopyDescent.realizationIso hcof hfib

example {X Y : Cᵒᵖ × C} (f : X ⟶ Y)
    (hs : weakEquivalences C f.1.unop) (ht : weakEquivalences C f.2) :
    IsIso ((OrdinaryBarHomotopyDescent.functor hcof hfib).map f) :=
  OrdinaryBarHomotopyDescent.map_isIso hcof hfib f hs ht

example : RightResolutionMapping.projection ⋙
    OrdinaryBarHomotopyDescent.functor (C := C) hcof hfib ≅
      OrdinaryBarHomotopyDescent.presentation (C := C) :=
  OrdinaryBarHomotopyDescent.presentationIso hcof hfib

example {X Y : RightResolutionMapping.Index C} (f g : X ⟶ Y)
    (h : RightResolutionMapping.projection.map f = RightResolutionMapping.projection.map g) :
    (OrdinaryBarHomotopyDescent.presentation (C := C)).map f =
      (OrdinaryBarHomotopyDescent.presentation (C := C)).map g :=
  OrdinaryBarHomotopyDescent.presentation_map_eq_of_base_eq hcof hfib f g h

example {X Y : RightResolutionMapping.Index C} (f : X ⟶ Y)
    [IsIso (RightResolutionMapping.projection.map f)] :
    IsIso ((OrdinaryBarHomotopyDescent.presentation (C := C)).map f) :=
  OrdinaryBarHomotopyDescent.presentation_map_isIso_of_base_isIso hcof hfib f
end Base

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.SmallKanHomotopy,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarHomotopyDescent]
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
  unless modules.size == expected.size do
    throwError "Missing ordinary bar homotopy descent modules"
  logInfo m!"Ordinary bar homotopy descent audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
