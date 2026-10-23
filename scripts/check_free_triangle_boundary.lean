import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeTriangleBoundary

universe v u
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.HomotopyFunctionComplex

-- Model-independent identities for arbitrary object and Hom universes.
section General
variable (D : Type u) [Category.{v} D]
open FreePathResolutionDegreeTwo
example : faceOne D ⋙ lowerZero D = faceZero D ⋙ lowerZero D := faceOne_lowerZero D
example : faceTwo D ⋙ lowerZero D = faceZero D ⋙ lowerOne D := faceTwo_lowerZero D
example : faceTwo D ⋙ lowerOne D = faceOne D ⋙ lowerOne D := faceTwo_lowerOne D
example : degeneracyZero D ⋙ faceZero D = 𝟭 _ := degeneracyZero_faceZero D
example : degeneracyZero D ⋙ faceOne D = 𝟭 _ := degeneracyZero_faceOne D
example : degeneracyZero D ⋙ faceTwo D = lowerOne D ⋙ FreePathResolution.duplicate D :=
  degeneracyZero_faceTwo D
example : degeneracyOne D ⋙ faceZero D = lowerZero D ⋙ FreePathResolution.duplicate D :=
  degeneracyOne_faceZero D
example : degeneracyOne D ⋙ faceOne D = 𝟭 _ := degeneracyOne_faceOne D
example : degeneracyOne D ⋙ faceTwo D = 𝟭 _ := degeneracyOne_faceTwo D
example : FreePathResolution.duplicate D ⋙ degeneracyZero D =
    FreePathResolution.duplicate D ⋙ degeneracyOne D := degeneracy_overlap D
end General

-- Actual edge comparisons; no extra source assumptions or large SSet model.
section Actual
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})
open OrdinaryBarFreeTriangleBoundary

example : edge01 (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₀ = vertex0 hcof hfib P :=
  edge01_zero hcof hfib P

example : edge01 (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₁ = vertex1 hcof hfib P :=
  edge01_one hcof hfib P

example : edge02 (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₀ = vertex0 hcof hfib P :=
  edge02_zero hcof hfib P

example : edge02 (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₁ = vertex2 hcof hfib P :=
  edge02_one hcof hfib P

example : edge12 (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₀ = vertex1 hcof hfib P :=
  edge12_zero hcof hfib P

example : edge12 (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₁ = vertex2 hcof hfib P :=
  edge12_one hcof hfib P

example : FreePathResolutionDegreeTwo.degeneracyZero (Cᵒᵖ × C) ⋙
    edge01 hcof hfib P = OrdinaryBarFreeResolutionComparison.comparison hcof hfib P :=
  degeneracyZero_edge01 hcof hfib P

example : FreePathResolutionDegreeTwo.degeneracyZero (Cᵒᵖ × C) ⋙
    edge02 hcof hfib P = OrdinaryBarFreeResolutionComparison.comparison hcof hfib P :=
  degeneracyZero_edge02 hcof hfib P

example : FreePathResolutionDegreeTwo.degeneracyZero (Cᵒᵖ × C) ⋙
    edge12 hcof hfib P = constantOne hcof hfib P :=
  degeneracyZero_edge12 hcof hfib P

example : FreePathResolutionDegreeTwo.degeneracyOne (Cᵒᵖ × C) ⋙
    edge01 hcof hfib P = constantZero hcof hfib P :=
  degeneracyOne_edge01 hcof hfib P

example : FreePathResolutionDegreeTwo.degeneracyOne (Cᵒᵖ × C) ⋙
    edge02 hcof hfib P = OrdinaryBarFreeResolutionComparison.comparison hcof hfib P :=
  degeneracyOne_edge02 hcof hfib P

example : FreePathResolutionDegreeTwo.degeneracyOne (Cᵒᵖ × C) ⋙
    edge12 hcof hfib P = OrdinaryBarFreeResolutionComparison.comparison hcof hfib P :=
  degeneracyOne_edge12 hcof hfib P

example : (FreePathResolution.duplicate (Cᵒᵖ × C) ⋙
    FreePathResolutionDegreeTwo.degeneracyZero (Cᵒᵖ × C)) ⋙ edge01 hcof hfib P =
      OrdinaryBarFreeDiagramExtension.freeCover hcof hfib P ⋙
        OrdinaryBarChoiceCategory.reindex hcof hfib
          (fst P (SSet.stdSimplex.obj (SimplexCategory.mk 1))) :=
  double_degeneracy_edge01 hcof hfib P

example : (FreePathResolution.duplicate (Cᵒᵖ × C) ⋙
    FreePathResolutionDegreeTwo.degeneracyZero (Cᵒᵖ × C)) ⋙ edge02 hcof hfib P =
      OrdinaryBarFreeDiagramExtension.freeCover hcof hfib P ⋙
        OrdinaryBarChoiceCategory.reindex hcof hfib
          (fst P (SSet.stdSimplex.obj (SimplexCategory.mk 1))) :=
  double_degeneracy_edge02 hcof hfib P

example : (FreePathResolution.duplicate (Cᵒᵖ × C) ⋙
    FreePathResolutionDegreeTwo.degeneracyZero (Cᵒᵖ × C)) ⋙ edge12 hcof hfib P =
      OrdinaryBarFreeDiagramExtension.freeCover hcof hfib P ⋙
        OrdinaryBarChoiceCategory.reindex hcof hfib
          (fst P (SSet.stdSimplex.obj (SimplexCategory.mk 1))) :=
  double_degeneracy_edge12 hcof hfib P
end Actual

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.FreePathResolutionDegreeTwo,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeTriangleBoundary]
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
    throwError "Missing free triangle boundary modules"
  logInfo m!"Free triangle boundary audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
