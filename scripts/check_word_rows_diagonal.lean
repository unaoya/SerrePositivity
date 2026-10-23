import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal
import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalAnodyne
import Lean.Util.CollectAxioms

universe u v w u' v' w'
noncomputable section
open CategoryTheory
open SerrePositivity SerrePositivity.SimplicialModel

section Generic
variable {C : Type u} [Category.{v} C] {M : Type w} [MonoidWithZero M]
  {E : Type u'} [Category.{v'} E] {N : Type w'} [MonoidWithZero N]
example : AmbientWords.map (𝟭 C) (MonoidWithZeroHom.id M) = 𝟭 (AmbientWords.Obj C M) :=
  AmbientWords.map_id
example (F : C ⥤ E) (h : M →*₀ N) :
    AmbientWords.map F h ⋙ AmbientWords.augmentation E N = AmbientWords.augmentation C M ⋙ F :=
  AmbientWords.map_augmentation F h
example : AmbientWords.toRetract C M ⋙ RetractWords.augmentation C M =
    AmbientWords.augmentation C M := AmbientWords.toRetract_augmentation
end Generic

open HomotopyFunctionComplex OrdinaryBarFreeResolutionSeed
open OrdinaryBarWordRowMaps OrdinaryBarWordRows
variable (C : Type u) [Category.{v} C] (X Y : D C)
example : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} := rows C X Y
example {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    rowMap C X Y θ ≫ (augmentation C X Y).app m =
      (augmentation C X Y).app n ≫ (targetRows C X Y).map θ :=
  (augmentation C X Y).naturality θ
example (n : SimplexCategoryᵒᵖ) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((augmentation C X Y).app n)) :=
  localized_augmentation_app C X Y n
example : targetDiagonal C X Y ≅ UniverseLift.obj.{max u v} (OrdinaryBarSourceHom.hom C X Y) :=
  targetDiagonalIso C X Y
example : diagonal C X Y ≅ OrdinaryBarAmbientWordComparison.hom C X Y :=
  OrdinaryBarWordRowsDiagonal.comparisonIso C X Y
example : OrdinaryBarAmbientWordComparison.augmentation C X Y =
    OrdinaryBarWordRowsDiagonal.toSource C X Y ≫ OrdinaryBarSourceHom.augmentation C X Y :=
  OrdinaryBarWordRowsDiagonal.augmentation_factorization C X Y

-- Unconditional lifting proofs: no ModelCategory SSet is an input.
example {E B : SSet.{v}} (p : E ⟶ B) (hp : SSet.modelCategoryQuillen.J.rlp p) (n : ℕ) :
    SSet.modelCategoryQuillen.J.rlp (Reedy.relativeMatchingMap Reedy.simplexOp
      (Opposite.op (SimplexCategory.mk n)) (BisimplicialModel.internalHomRight.map p)) :=
  BisimplicialModel.relativeMatching_horn_rlp p hp n
example {A B : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (f : A ⟶ B)
    (hf : Reedy.reedyLeft Reedy.simplexOp SSet.anodyneExtensions f) :
    SSet.anodyneExtensions (BisimplicialModel.diagonal.map f) :=
  BisimplicialModel.diagonal_map_anodyne f hf

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.CategoryTheory.Presentation.AmbientWordFunctoriality,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarWordRowMaps,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarSourceHom,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarWordRows,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalAnodyne]
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
  unless modules.size == expected.size do throwError "Missing word row and diagonal modules"
  logInfo m!"Word rows and diagonal audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
