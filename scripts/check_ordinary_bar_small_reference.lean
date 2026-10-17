import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open OrdinaryBarSmallReference OrdinaryBarSmallAction

variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

-- The reference is the original small Kan replacement value, not a shrink of the bar.
example (X : Cᵒᵖ × C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (toReference hcof hfib X)) :=
  toReference_isIso hcof hfib X

-- Localized Hom between large bar values is small in the original Hom universe.
include hcof hfib in
example (X Y : Cᵒᵖ × C) :
    Small.{v} (AnodyneHomotopy.anodyneQ.obj (OrdinaryResolutionBar.functor.obj X) ⟶
      AnodyneHomotopy.anodyneQ.obj (OrdinaryResolutionBar.functor.obj Y)) :=
  OrdinaryBarSmallReference.small_localizedHom hcof hfib X Y

-- Every base arrow is represented by an actual small simplicial map.
example {X Y : Cᵒᵖ × C} (f : X ⟶ Y) :
    value hcof hfib X ⟶ value hcof hfib Y := arrow hcof hfib f

example (X : Cᵒᵖ × C) :
    Nonempty (SSet.Homotopy (arrow hcof hfib (𝟙 X)) (𝟙 (value hcof hfib X))) :=
  arrow_id_homotopy hcof hfib X

example {X Y Z : Cᵒᵖ × C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Nonempty (SSet.Homotopy (arrow hcof hfib (f ≫ g))
      (arrow hcof hfib f ≫ arrow hcof hfib g)) :=
  arrow_comp_homotopy hcof hfib f g

example {X Y : Cᵒᵖ × C} (f : X ⟶ Y) :
    Nonempty (SSet.Homotopy
      (OrdinaryResolutionBar.functor.map f ≫ toReference hcof hfib Y)
      (toReference hcof hfib X ≫ UniverseLift.map.{max u v} (arrow hcof hfib f))) :=
  square_homotopy hcof hfib f

include hcof hfib in
example {X Y : Cᵒᵖ × C} (f : X ⟶ Y)
    (hs : weakEquivalences C f.1.unop) (ht : weakEquivalences C f.2) :
    weakEquivalences SSet.{v} (arrow hcof hfib f) :=
  arrow_weakEquivalence hcof hfib f hs ht

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarSmallReference,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarSmallAction]
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
    throwError "Missing ordinary bar small reference modules"
  logInfo m!"Ordinary bar small reference audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
