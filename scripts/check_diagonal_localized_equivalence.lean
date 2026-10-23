import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarWordDiagonalEquivalence
import Lean.Util.CollectAxioms

universe u v
noncomputable section
open CategoryTheory CategoryTheory.Limits
open SerrePositivity SerrePositivity.SimplicialModel

-- No model structure is assumed in this value universe.
example {A T E B : SSet.{v}} (i : A ⟶ T) [Mono i]
    (hi : IsIso (AnodyneHomotopy.anodyneQ.map i)) (p : E ⟶ B)
    (hp : SSet.modelCategoryQuillen.J.rlp p)
    (hB : SSet.modelCategoryQuillen.J.rlp (terminal.from B)) : HasLiftingProperty i p :=
  KanLocalizedMonoLifting.hasLiftingProperty i hi p hp hB
example {A B : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (f : A ⟶ B) :
    Reedy.reedyLeft Reedy.simplexOp KanTestLiftingClass.localizedMonos f ↔
      Reedy.reedyLeft Reedy.simplexOp (MorphismProperty.monomorphisms _) f ∧
        ∀ n, IsIso (AnodyneHomotopy.anodyneQ.map (f.app n)) := LocalizedMonoReedy.reedy_iff f
example : MorphismProperty.IsWeakFactorizationSystem
    BisimplicialModel.BoundaryFactorization.left.{v}
    BisimplicialModel.BoundaryFactorization.right.{v} :=
  BisimplicialModel.BoundaryFactorization.reedy_wfs
example {A B : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (f : A ⟶ B)
    (hf : ∀ n, IsIso (AnodyneHomotopy.anodyneQ.map (f.app n))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (BisimplicialModel.diagonal.map f)) :=
  BisimplicialModel.localized_diagonal_map f hf

open HomotopyFunctionComplex OrdinaryBarFreeResolutionSeed
variable (C : Type u) [Category.{v} C] (X Y : D C)
example : IsIso (AnodyneHomotopy.anodyneQ.map
    (OrdinaryBarWordRows.diagonalAugmentation C X Y)) :=
  OrdinaryBarWordDiagonalEquivalence.diagonal_augmentation_isIso C X Y
example : IsIso (AnodyneHomotopy.anodyneQ.map (OrdinaryBarWordRowsDiagonal.toSource C X Y)) :=
  OrdinaryBarWordDiagonalEquivalence.toSource_isIso C X Y
example : IsIso (AnodyneHomotopy.anodyneQ.map
    (OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X Y)) ↔
      IsIso (AnodyneHomotopy.anodyneQ.map (OrdinaryBarSourceHom.augmentation C X Y)) :=
  OrdinaryBarWordDiagonalEquivalence.small_augmentation_isIso_iff_source C X Y

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanLocalizedMonoLifting,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalKanTests,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.LocalizedMonoReedy,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryReedyFactorization,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarWordDiagonalEquivalence]
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
  unless modules.size == expected.size do throwError "Missing model-free diagonal comparison modules"
  logInfo m!"Model-free diagonal comparison audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
