module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal

/-! # The actual diagonal word comparison is inverted without a large SSet model structure -/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordDiagonalEquivalence
open OrdinaryBarFreeResolutionSeed
variable (C : Type u) [Category.{v} C] (X Y : D C)

lemma diagonal_augmentation_isIso : IsIso (AnodyneHomotopy.anodyneQ.map
    (OrdinaryBarWordRows.diagonalAugmentation C X Y)) :=
  BisimplicialModel.localized_diagonal_map (OrdinaryBarWordRows.augmentation C X Y)
    (OrdinaryBarWordRows.localized_augmentation_app C X Y)

lemma toSource_isIso : IsIso (AnodyneHomotopy.anodyneQ.map
    (OrdinaryBarWordRowsDiagonal.toSource C X Y)) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (OrdinaryBarWordRows.diagonalAugmentation C X Y)) := diagonal_augmentation_isIso C X Y
  rw [OrdinaryBarWordRowsDiagonal.toSource, OrdinaryBarWordRows.toSource,
    Functor.map_comp, Functor.map_comp]
  infer_instance

lemma augmentation_isIso_iff_source :
    IsIso (AnodyneHomotopy.anodyneQ.map (OrdinaryBarAmbientWordComparison.augmentation C X Y)) ↔
      IsIso (AnodyneHomotopy.anodyneQ.map (OrdinaryBarSourceHom.augmentation C X Y)) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (OrdinaryBarWordRowsDiagonal.toSource C X Y)) := toSource_isIso C X Y
  rw [OrdinaryBarWordRowsDiagonal.augmentation_factorization, Functor.map_comp]
  exact isIso_comp_left_iff _ _

lemma small_augmentation_isIso_iff_source :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X Y)) ↔
        IsIso (AnodyneHomotopy.anodyneQ.map (OrdinaryBarSourceHom.augmentation C X Y)) :=
  (OrdinaryBarAmbientWordComparison.localized_small_iff_words C X Y).trans
    (augmentation_isIso_iff_source C X Y)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordDiagonalEquivalence
