import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.WordPresentationDiagram
import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarWordPresentation

universe u v w u' v' w' uD vD
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity SerrePositivity.SimplicialModel

section General
variable (C : Type u) [Category.{v} C] (M : Type w) [MonoidWithZero M]
example : Category.{max u v w} (RetractWords.Small C M) := inferInstance
example : RetractWords.Obj C M ⥤ C := RetractWords.augmentation C M
example : RetractWords.sourceFunctor C M ⋙ RetractWords.augmentation C M = 𝟭 C :=
  RetractWords.source_augmentation C M
example (X : C) :
    (RetractWords.quotient C M).map (RetractWords.section_ C M X ≫ RetractWords.projection C M X) =
      𝟙 _ := by
  exact (CategoryTheory.Quotient.sound (RetractWords.Rel C M)
    (RetractWords.Rel.split X)).trans ((RetractWords.quotient C M).map_id _)
example {D : Type uD} [Category.{vD} D] (R : RetractWords.Realization C M D) :
    RetractWords.Small C M ⥤ D := R.smallFunctor
example : RetractWords.map (𝟭 C) (MonoidWithZeroHom.id M) = 𝟭 (RetractWords.Obj C M) :=
  RetractWords.map_id
variable {C M} {C' : Type u'} [Category.{v'} C'] {N : Type w'} [MonoidWithZero N]
example (F : C ⥤ C') (h : M →*₀ N) : RetractWords.Obj C M ⥤ RetractWords.Obj C' N :=
  RetractWords.map F h
example (F : C ⥤ C') (h : M →*₀ N) :
    RetractWords.map F h ⋙ RetractWords.map (𝟭 C') (MonoidWithZeroHom.id N) =
      RetractWords.map F h := by rw [RetractWords.map_id, Functor.comp_id]
end General

section Simplicial
variable (C : Type u) [Category.{v} C]
example : SimplicialObject Cat.{max u v w, u} := WordPresentationDiagram.diagram.{u, v, w} C
example (X Y : C) : SSet.{max u v w} := WordPresentationDiagram.smallHom.{u, v, w} C X Y
example (W X Y Z : C) :
    WordPresentationDiagram.composition.{u, v, w} C W X Y ▷
        WordPresentationDiagram.smallHom C Y Z ≫ WordPresentationDiagram.composition C W Y Z =
      (α_ (WordPresentationDiagram.smallHom C W X) (WordPresentationDiagram.smallHom C X Y)
        (WordPresentationDiagram.smallHom C Y Z)).hom ≫
        WordPresentationDiagram.smallHom C W X ◁ WordPresentationDiagram.composition C X Y Z ≫
          WordPresentationDiagram.composition C W X Z :=
  WordPresentationDiagram.composition_assoc C W X Y Z
end Simplicial

section Actual
open HomotopyFunctionComplex OrdinaryBarWordPresentation
open OrdinaryBarRetractSystem FreeGeneratorCategories OrdinaryBarFreeResolutionSeed
open OrdinaryBarChoiceBoundaryGluing
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) (n : ℕ) (k : SimplexCategoryᵒᵖ) (t : (parameters P n).obj k)
example : smallCategory (C := C) n k ⥤ Type v := smallEvaluation hcof hfib P n k t
example (X : smallCategory (C := C) n k) :
    (smallEvaluation hcof hfib P n k t).obj X = (small hcof hfib X).obj k := rfl
example {X Y : degree (D C) (n + 1)} (f : X ⟶ Y) :
    (largeEvaluation (C := C) hcof hfib P n k t).map
      ((RetractWords.quotient (degree (D C) (n + 1)) (WordSegment.degree.{max u v} k)).map
        (RetractWords.section_ _ _ X ≫ RetractWords.source _ _ f ≫
          RetractWords.projection _ _ Y)) =
      (section_ hcof hfib X).app k ≫
        (WordPresentationRealization.parameterEvaluation k t).map
          (OrdinaryBarFreeAmbientFamilies.family hcof hfib P n f) ≫
        (projection hcof hfib Y).app k := largeEvaluation_transferred hcof hfib P n k t f
end Actual

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.WordPresentationRealization,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.WordPresentationDiagram,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarWordPresentation]
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
  unless modules.size == expected.size do throwError "Missing retract word presentation modules"
  logInfo m!"Retract word presentation audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
