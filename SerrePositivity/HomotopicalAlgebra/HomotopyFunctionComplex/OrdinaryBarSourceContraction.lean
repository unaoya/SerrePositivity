module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceExtraDegeneracy
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordDiagonalEquivalence
public import SerrePositivity.HomotopicalAlgebra.Simplicial.OppositeHomotopy

/-! # The actual source and small-vertex augmentations are localized isomorphisms -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceContraction
open OrdinaryBarFreeResolutionSeed OppositeHomotopy
variable (C : Type u) [Category.{v} C] (X Y : D C)

abbrev baseReverseIso : reverse (OrdinaryBarDiagonalHomAugmentation.baseHom C X Y) ≅
    OrdinaryBarDiagonalHomAugmentation.baseHom C X Y :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro n m θ; rfl)

lemma augmentation_factorization : OrdinaryBarSourceHom.augmentation C X Y =
    (doubleIso (UniverseLift.obj.{max u v} (OrdinaryBarSourceHom.hom C X Y))).inv ≫
      reverseMap (OrdinaryBarSourceExtraDegeneracy.augmented C X Y).hom ≫
        (baseReverseIso C X Y).hom := by
  ext n f
  rfl

lemma source_augmentation_isIso : IsIso (AnodyneHomotopy.anodyneQ.map
    (OrdinaryBarSourceHom.augmentation C X Y)) := by
  have := localized_reversed_augmentation_isIso
    (OrdinaryBarSourceExtraDegeneracy.extraDegeneracy C X Y)
  rw [augmentation_factorization]
  simp only [AnodyneHomotopy.anodyneQ.map_comp]
  infer_instance

lemma word_augmentation_isIso : IsIso (AnodyneHomotopy.anodyneQ.map
    (OrdinaryBarAmbientWordComparison.augmentation C X Y)) :=
  (OrdinaryBarWordDiagonalEquivalence.augmentation_isIso_iff_source C X Y).mpr
    (source_augmentation_isIso C X Y)

lemma small_augmentation_isIso : IsIso (AnodyneHomotopy.anodyneQ.map
    (OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X Y)) :=
  (OrdinaryBarWordDiagonalEquivalence.small_augmentation_isIso_iff_source C X Y).mpr
    (source_augmentation_isIso C X Y)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceContraction
