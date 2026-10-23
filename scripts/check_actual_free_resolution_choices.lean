import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeResolutionChoices

universe v u
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.HomotopyFunctionComplex
open FreeGeneratorCategories FreeGeneratorFaces OrdinaryBarFreeDiagramExtension
open OrdinaryBarChoiceBoundaryGluing OrdinaryBarFreeResolutionDegeneracyValues

variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})

-- No seed, coherence witness, or extra hypothesis on the source model is an input.
example : OrdinaryBarFreeResolutionTower.Seed (C := C) hcof hfib (Cᵒᵖ × C) P :=
  OrdinaryBarFreeResolutionSeed.seed C hcof hfib P

example : degree (Cᵒᵖ × C) 1 ⥤ target (C := C) hcof hfib (parameters P 0) :=
  OrdinaryBarFreeResolutionChoices.diagram hcof hfib P 0

example (n : ℕ) : degree (Cᵒᵖ × C) (n + 1) ⥤
    target (C := C) hcof hfib (parameters P n) :=
  OrdinaryBarFreeResolutionChoices.diagram hcof hfib P n

example (n : ℕ) (i : Fin (n + 2)) :
    OrdinaryBarFreeResolutionChoices.diagram hcof hfib P (n + 1) ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.δ i) =
    fixedFace (Cᵒᵖ × C) (n + 1) i ⋙ OrdinaryBarFreeResolutionChoices.diagram hcof hfib P n :=
  OrdinaryBarFreeResolutionChoices.diagram_face hcof hfib P n i

example (n : ℕ) (i : Fin (n + 1)) : degeneracyFunctor (Cᵒᵖ × C) n i ⋙
    OrdinaryBarFreeResolutionChoices.diagram hcof hfib P (n + 1) =
      OrdinaryBarFreeResolutionChoices.diagram hcof hfib P n ⋙
        OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ sigma n i) :=
  OrdinaryBarFreeResolutionChoices.diagram_degeneracy hcof hfib P n i

example (n : ℕ) : OrdinaryBarFreeResolutionChoices.diagram hcof hfib P n ⋙
    OrdinaryBarChoiceCategory.projection hcof hfib (parameters P n) =
      OrdinaryBarFreeResolutionChoices.augmentation (C := C) n :=
  OrdinaryBarFreeResolutionChoices.projection_eq_augmentation hcof hfib P n

example : OrdinaryBarFreeResolutionChoices.diagram hcof hfib P 0 =
    OrdinaryBarFreeResolutionSeed.zero C hcof hfib P := rfl
example : OrdinaryBarFreeResolutionChoices.diagram hcof hfib P 1 =
    OrdinaryBarFreeResolutionSeed.one C hcof hfib P := rfl

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeResolutionSeed,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeResolutionChoices]
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
    throwError "Missing actual free resolution choice modules"
  logInfo m!"Actual free resolution choices audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
