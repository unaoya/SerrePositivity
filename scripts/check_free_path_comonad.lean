import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionFaces

universe v u v' u'
noncomputable section
open CategoryTheory
open HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

-- Mixed object/Hom universes and arbitrary ordinary functors; no model structure is needed.
example {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (F : C ⥤ D) :
    FreePathResolution.map F ⋙ FreePathResolution.counit D =
      FreePathResolution.counit C ⋙ F := FreePathResolution.counit_naturality F

example {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (F : C ⥤ D) :
    FreePathResolution.map F ⋙ FreePathResolution.duplicate D =
      FreePathResolution.duplicate C ⋙ FreePathResolution.map (FreePathResolution.map F) :=
  FreePathResolution.duplicate_naturality F

example {C : Type u} [Category.{v} C] :
    FreePathResolution.duplicate C ⋙ FreePathResolution.counit (Paths C) = 𝟭 (Paths C) :=
  FreePathResolution.left_counit

example {C : Type u} [Category.{v} C] :
    FreePathResolution.duplicate C ⋙ FreePathResolution.map (FreePathResolution.counit C) =
      𝟭 (Paths C) := FreePathResolution.right_counit

example {C : Type u} [Category.{v} C] :
    FreePathResolution.duplicate C ⋙ FreePathResolution.map (FreePathResolution.duplicate C) =
      FreePathResolution.duplicate C ⋙ FreePathResolution.duplicate (Paths C) :=
  FreePathResolution.coassociativity

-- An actual Mathlib Comonad, rather than an unproved package of prospective face maps.
example : Comonad Cat.{max u v, u} := FreePathResolution.comonad

section Actual
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

example (P : SSet.{max u v}) :
    OrdinaryBarFreeResolutionFaces.faceZero (C := C) hcof hfib P ⋙
        OrdinaryBarChoiceCategory.projection hcof hfib P =
      OrdinaryBarFreeResolutionFaces.faceOne hcof hfib P ⋙
        OrdinaryBarChoiceCategory.projection hcof hfib P :=
  OrdinaryBarFreeResolutionFaces.projection_equal hcof hfib P

example (P : SSet.{max u v}) :
    FreePathResolution.duplicate (Cᵒᵖ × C) ⋙ OrdinaryBarFreeResolutionFaces.faceZero hcof hfib P =
      OrdinaryBarFreeDiagramExtension.freeCover hcof hfib P :=
  OrdinaryBarFreeResolutionFaces.degeneracy_faceZero hcof hfib P

example (P : SSet.{max u v}) :
    FreePathResolution.duplicate (Cᵒᵖ × C) ⋙ OrdinaryBarFreeResolutionFaces.faceOne hcof hfib P =
      OrdinaryBarFreeDiagramExtension.freeCover hcof hfib P :=
  OrdinaryBarFreeResolutionFaces.degeneracy_faceOne hcof hfib P
end Actual

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreePathResolution,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionFaces]
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
    throwError "Missing free path comonad modules"
  logInfo m!"Free path comonad audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
