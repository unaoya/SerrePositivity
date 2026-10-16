import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarLabelSurjectivity

universe v u vH uH
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.SimplicialModel

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
  [Q.IsLocalization (weakEquivalences C)]

-- The source model alone supplies representatives for every degree and every pair.
example (R : OrdinaryResolutionPairs.Index (C := C)) (n : SimplexCategoryᵒᵖ) :
    Function.Surjective (OrdinaryMappingClassLabel.label Q R n) :=
  OrdinaryBarLabelSurjectivity.raw_label_surjective Q R n

example (b : Cᵒᵖ × C) (n : SimplexCategoryᵒᵖ) :
    Function.Surjective (OrdinaryBarMappingClasses.label Q b n) :=
  OrdinaryBarLabelSurjectivity.label_surjective Q b n

example (b : Cᵒᵖ × C) :
    Function.Surjective (OrdinaryBarMappingClasses.piZeroLabel Q b) :=
  OrdinaryBarLabelSurjectivity.piZeroLabel_surjective Q b

example :
    OrdinaryBarMappingClasses.coarseQuotient Q ⋙ SSet.uliftFunctor.{max u v, v} ≅
      LocalizedHomDiagram.spaces Q ⋙ SSet.uliftFunctor.{max u v, v} :=
  OrdinaryBarLabelSurjectivity.coarseLiftIso Q

example : OrdinaryBarMappingClasses.coarseProjection Q ≫
    (OrdinaryBarLabelSurjectivity.coarseLiftIso Q).hom =
      OrdinaryBarMappingClasses.augmentation Q :=
  OrdinaryBarLabelSurjectivity.coarseProjection_comparison Q

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.DiagramQuotient,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarLabelSurjectivity]
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
    throwError "Missing ordinary bar label surjectivity modules"
  logInfo m!"Ordinary bar label surjectivity audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
