module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockComposition
public import SerrePositivity.EInfinity.SimplicialLocalization.DKHammockCoefficientComparison
public import SerrePositivity.EInfinity.Hammock.WeakTensor

/-!
# 元の DK hammock 比較の積と合成の正方形

概要：元の左右 span とその積は anodyne 局所化内で同じ合成を回収する。
方針：元の右射とその積を反転し、証明済みの二つの合成正方形を使う。
規約：局所化関手の積保存や元の射の零単体の厳密な合成保存を仮定しない。
使われ方：元の代数射に沿う両端点の高次自然性。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory MonoidalCategory SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def dkHammockColimitComparisonIso (X Y : C.category) :
    AnodyneHomotopy.anodyneQ.obj (localizationHom C X Y) ≅
      AnodyneHomotopy.anodyneQ.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences X Y) := by
  have := Hammock.anodyneQ_map_isIso_of_weak (freeHammockDiagonalComparison C X Y)
    (freeHammockDiagonalComparison_isWeakHomotopyEquivalence C X Y)
  have := Hammock.anodyneQ_map_isIso_of_weak (freeHammockDiagonalAugmentation C X Y)
    (freeHammockDiagonalAugmentation_isWeakHomotopyEquivalence C X Y)
  exact (asIso (AnodyneHomotopy.anodyneQ.map
    (freeHammockDiagonalComparison C X Y))).symm ≪≫
      asIso (AnodyneHomotopy.anodyneQ.map (freeHammockDiagonalAugmentation C X Y))

lemma dkHammockColimitComparisonIso_fac (X Y : C.category) :
    AnodyneHomotopy.anodyneQ.map (freeHammockDiagonalComparison C X Y) ≫
        (dkHammockColimitComparisonIso C X Y).hom =
      AnodyneHomotopy.anodyneQ.map (freeHammockDiagonalAugmentation C X Y) := by
  have := Hammock.anodyneQ_map_isIso_of_weak (freeHammockDiagonalComparison C X Y)
    (freeHammockDiagonalComparison_isWeakHomotopyEquivalence C X Y)
  change AnodyneHomotopy.anodyneQ.map _ ≫ (inv (AnodyneHomotopy.anodyneQ.map _) ≫ _) = _
  exact IsIso.hom_inv_id_assoc _ _

def dkHammockProductComparisonIso (X Y Z : C.category) :
    AnodyneHomotopy.anodyneQ.obj (localizationHom C X Y ⊗ localizationHom C Y Z) ≅
      AnodyneHomotopy.anodyneQ.obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences X Y ⊗
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences Y Z) := by
  have := Hammock.anodyneQ_map_isIso_of_weak
    (freeHammockDiagonalComparison C X Y ⊗ₘ freeHammockDiagonalComparison C Y Z)
    (Hammock.weakTensor (freeHammockDiagonalComparison_isWeakHomotopyEquivalence C X Y)
      (freeHammockDiagonalComparison_isWeakHomotopyEquivalence C Y Z))
  have := Hammock.anodyneQ_map_isIso_of_weak
    (freeHammockDiagonalAugmentation C X Y ⊗ₘ freeHammockDiagonalAugmentation C Y Z)
    (Hammock.weakTensor (freeHammockDiagonalAugmentation_isWeakHomotopyEquivalence C X Y)
      (freeHammockDiagonalAugmentation_isWeakHomotopyEquivalence C Y Z))
  exact (asIso (AnodyneHomotopy.anodyneQ.map
    (freeHammockDiagonalComparison C X Y ⊗ₘ freeHammockDiagonalComparison C Y Z))).symm ≪≫
      asIso (AnodyneHomotopy.anodyneQ.map
        (freeHammockDiagonalAugmentation C X Y ⊗ₘ freeHammockDiagonalAugmentation C Y Z))

lemma dkHammockProductComparisonIso_fac (X Y Z : C.category) :
    AnodyneHomotopy.anodyneQ.map
        (freeHammockDiagonalComparison C X Y ⊗ₘ freeHammockDiagonalComparison C Y Z) ≫
      (dkHammockProductComparisonIso C X Y Z).hom =
    AnodyneHomotopy.anodyneQ.map
      (freeHammockDiagonalAugmentation C X Y ⊗ₘ freeHammockDiagonalAugmentation C Y Z) := by
  have := Hammock.anodyneQ_map_isIso_of_weak
    (freeHammockDiagonalComparison C X Y ⊗ₘ freeHammockDiagonalComparison C Y Z)
    (Hammock.weakTensor (freeHammockDiagonalComparison_isWeakHomotopyEquivalence C X Y)
      (freeHammockDiagonalComparison_isWeakHomotopyEquivalence C Y Z))
  change AnodyneHomotopy.anodyneQ.map _ ≫ (inv (AnodyneHomotopy.anodyneQ.map _) ≫ _) = _
  exact IsIso.hom_inv_id_assoc _ _

lemma dkHammockComparison_composition (X Y Z : C.category) :
    AnodyneHomotopy.anodyneQ.map (localizationComposition C X Y Z) ≫
        (dkHammockColimitComparisonIso C X Z).hom =
      (dkHammockProductComparisonIso C X Y Z).hom ≫
        AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition C.weakEquivalences X Y Z) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := Hammock.anodyneQ_map_isIso_of_weak
    (freeHammockDiagonalComparison C X Y ⊗ₘ freeHammockDiagonalComparison C Y Z)
    (Hammock.weakTensor (freeHammockDiagonalComparison_isWeakHomotopyEquivalence C X Y)
      (freeHammockDiagonalComparison_isWeakHomotopyEquivalence C Y Z))
  apply (cancel_epi (Q.map
    (freeHammockDiagonalComparison C X Y ⊗ₘ freeHammockDiagonalComparison C Y Z))).mp
  rw [← Category.assoc, ← Q.map_comp, ← freeHammockDiagonalComposition_comparison,
    Q.map_comp, Category.assoc, dkHammockColimitComparisonIso_fac, ← Q.map_comp,
    freeHammockDiagonalComposition_augmentation, Q.map_comp,
    ← dkHammockProductComparisonIso_fac, Category.assoc]

lemma dkHammockComparisonIso_reduction (X Y : C.category) :
    (dkHammockColimitComparisonIso C X Y).hom ≫
        AnodyneHomotopy.anodyneQ.map (Hammock.reducedColimitIso C.weakEquivalences X Y).hom =
      (dkHammockComparisonIso C X Y).hom := by
  have := Hammock.anodyneQ_map_isIso_of_weak (freeHammockDiagonalComparison C X Y)
    (freeHammockDiagonalComparison_isWeakHomotopyEquivalence C X Y)
  apply (cancel_epi (AnodyneHomotopy.anodyneQ.map
    (freeHammockDiagonalComparison C X Y))).mp
  rw [← Category.assoc, dkHammockColimitComparisonIso_fac, ← Functor.map_comp,
    dkHammockComparisonIso_fac]
  rfl

end SerrePositivity.EInfinity.SimplicialLocalization
