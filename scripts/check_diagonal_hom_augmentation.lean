import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarDiagonalHomAugmentation
import Lean.Util.CollectAxioms

universe u v uH vH
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.SimplicialModel
open OrdinaryBarFreeResolutionSeed OrdinaryBarFixedWordResolution OrdinaryBarDiagonalAmbientHom
open OrdinaryBarDiagonalHomRetraction OrdinaryBarDiagonalHomAugmentation

-- All consumers assume only a category, with independent object and Hom universes.
variable (C : Type u) [Category.{v} C] (X Y Z : D C)

example : inclusion C X Y ≫ transfer C X Y = 𝟙 (hom C X Y) := inclusion_transfer C X Y
example : SSet.Homotopy (𝟙 (ambientHom C X Y)) (transfer C X Y ≫ inclusion C X Y) :=
  contraction C X Y
example {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    L.obj (ambientHom C X Y) ≅ L.obj (hom C X Y) := comparisonIso C L hL X Y
example : IsIso (AnodyneHomotopy.anodyneQ.map (transfer C X Y)) :=
  localized_transfer_isIso C X Y
example : IsIso (AnodyneHomotopy.anodyneQ.map (inclusion C X Y)) :=
  localized_inclusion_isIso C X Y
example : hom C X Y ⟶ baseHom C X Y := smallAugmentation C X Y
example : ambientHom C X Y ⟶ baseHom C X Y := ambientAugmentation C X Y
example : transfer C X Y ≫ smallAugmentation C X Y = ambientAugmentation C X Y :=
  transfer_augmentation C X Y
example : inclusion C X Y ≫ ambientAugmentation C X Y = smallAugmentation C X Y :=
  inclusion_augmentation C X Y
example : composition C X Y Z ≫ smallAugmentation C X Z =
    (smallAugmentation C X Y ⊗ₘ smallAugmentation C Y Z) ≫ baseComposition C X Y Z :=
  augmentation_composition C X Y Z
example : identity C X ≫ smallAugmentation C X X = baseIdentity C X := augmentation_identity C X
example : IsIso (AnodyneHomotopy.anodyneQ.map (smallAugmentation C X Y)) ↔
    IsIso (AnodyneHomotopy.anodyneQ.map (ambientAugmentation C X Y)) :=
  localized_small_iff_ambient C X Y

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarDiagonalAmbientHom,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarDiagonalHomRetraction,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFixedAugmentation,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarDiagonalHomAugmentation]
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
  unless modules.size == expected.size do throwError "Missing diagonal Hom augmentation modules"
  logInfo m!"Diagonal Hom augmentation audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
