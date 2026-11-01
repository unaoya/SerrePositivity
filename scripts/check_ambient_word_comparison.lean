import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarAmbientWordComparison
import Lean.Util.CollectAxioms

universe u v w u' v' w'
noncomputable section
open CategoryTheory
open SerrePositivity SerrePositivity.SimplicialModel

section General
variable (C : Type u) [Category.{v} C] (M : Type w) [MonoidWithZero M] (X Y : C)
example :
    ((AmbientWords.sourceFunctor C M).obj X ⟶ (AmbientWords.sourceFunctor C M).obj Y) ≃
      ((RetractWords.sourceFunctor C M).obj X ⟶ (RetractWords.sourceFunctor C M).obj Y) :=
  AmbientWords.ambientHomEquiv C M X Y
example (f : (AmbientWords.sourceFunctor C M).obj X ⟶ (AmbientWords.sourceFunctor C M).obj Y) :
    AmbientWords.decodeHom C M ((AmbientWords.toRetract C M).map f) = f :=
  AmbientWords.decodeHom_toRetract C M f
example (f : (RetractWords.sourceFunctor C M).obj X ⟶ (RetractWords.sourceFunctor C M).obj Y) :
    (AmbientWords.toRetract C M).map (AmbientWords.decodeHom C M f) = f :=
  AmbientWords.toRetract_decodeHom C M f
example {E : Type u'} [Category.{v'} E] {N : Type w'} [MonoidWithZero N]
    (F : C ⥤ E) (h : M →*₀ N) :
    AmbientWords.map F h ⋙ AmbientWords.toRetract E N =
      AmbientWords.toRetract C M ⋙ RetractWords.map F h := AmbientWords.map_toRetract F h
end General

open HomotopyFunctionComplex OrdinaryBarFreeResolutionSeed
open OrdinaryBarAmbientWordComparison
variable (C : Type u) [Category.{v} C] (X Y : D C)
example : hom C X Y ≅ OrdinaryBarDiagonalAmbientHom.ambientHom C X Y := comparisonIso C X Y
example : hom C X Y ⟶ OrdinaryBarDiagonalHomAugmentation.baseHom C X Y := augmentation C X Y
example : IsIso (AnodyneHomotopy.anodyneQ.map
    (OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X Y)) ↔
      IsIso (AnodyneHomotopy.anodyneQ.map (augmentation C X Y)) := localized_small_iff_words C X Y
example {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (f : (hom C X Y).obj n) :
    (hom C X Y).map θ f =
      (AmbientWords.map (OrdinaryBarFixedSource.literalMap C θ)
        (MonoidWithZeroHom.id (WordSegment.degree.{max u v} n)) ⋙
      AmbientWords.map (𝟭 (FreeGeneratorCategories.degree (D C) (m.unop.len + 1)))
        (WordSegment.degreeMap θ)).map f := map_eq C θ f

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarAmbientWordComparison]
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
  unless modules.size == expected.size do throwError "Missing ambient word comparison modules"
  logInfo m!"Ambient word comparison audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
