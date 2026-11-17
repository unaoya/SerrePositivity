module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockComposition
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.DKHammockCoefficientComparison
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
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.SimplicialModel
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def dkHammockColimitComparisonIso (X Y : C.category) :
    AnodyneHomotopy.anodyneQ.obj (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C X Y) ≅
      AnodyneHomotopy.anodyneQ.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences X Y) := by
  have := _root_.SerrePositivity.EInfinity.Hammock.anodyneQ_map_isIso_of_weak (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C X Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison_isWeakHomotopyEquivalence C X Y)
  have := _root_.SerrePositivity.EInfinity.Hammock.anodyneQ_map_isIso_of_weak (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalAugmentation C X Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalAugmentation_isWeakHomotopyEquivalence C X Y)
  exact (asIso (AnodyneHomotopy.anodyneQ.map
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C X Y))).symm ≪≫
      asIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalAugmentation C X Y))

lemma dkHammockColimitComparisonIso_fac (X Y : C.category) :
    AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C X Y) ≫
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockColimitComparisonIso C X Y).hom =
      AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalAugmentation C X Y) := by
  have := _root_.SerrePositivity.EInfinity.Hammock.anodyneQ_map_isIso_of_weak (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C X Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison_isWeakHomotopyEquivalence C X Y)
  change AnodyneHomotopy.anodyneQ.map _ ≫ (inv (AnodyneHomotopy.anodyneQ.map _) ≫ _) = _
  exact IsIso.hom_inv_id_assoc _ _

def dkHammockProductComparisonIso (X Y Z : C.category) :
    AnodyneHomotopy.anodyneQ.obj (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C X Y ⊗ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C Y Z) ≅
      AnodyneHomotopy.anodyneQ.obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences X Y ⊗
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences Y Z) := by
  have := _root_.SerrePositivity.EInfinity.Hammock.anodyneQ_map_isIso_of_weak
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C X Y ⊗ₘ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C Y Z)
    (_root_.SerrePositivity.EInfinity.Hammock.weakTensor (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison_isWeakHomotopyEquivalence C X Y)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison_isWeakHomotopyEquivalence C Y Z))
  have := _root_.SerrePositivity.EInfinity.Hammock.anodyneQ_map_isIso_of_weak
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalAugmentation C X Y ⊗ₘ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalAugmentation C Y Z)
    (_root_.SerrePositivity.EInfinity.Hammock.weakTensor (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalAugmentation_isWeakHomotopyEquivalence C X Y)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalAugmentation_isWeakHomotopyEquivalence C Y Z))
  exact (asIso (AnodyneHomotopy.anodyneQ.map
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C X Y ⊗ₘ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C Y Z))).symm ≪≫
      asIso (AnodyneHomotopy.anodyneQ.map
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalAugmentation C X Y ⊗ₘ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalAugmentation C Y Z))

lemma dkHammockProductComparisonIso_fac (X Y Z : C.category) :
    AnodyneHomotopy.anodyneQ.map
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C X Y ⊗ₘ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C Y Z) ≫
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockProductComparisonIso C X Y Z).hom =
    AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalAugmentation C X Y ⊗ₘ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalAugmentation C Y Z) := by
  have := _root_.SerrePositivity.EInfinity.Hammock.anodyneQ_map_isIso_of_weak
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C X Y ⊗ₘ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C Y Z)
    (_root_.SerrePositivity.EInfinity.Hammock.weakTensor (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison_isWeakHomotopyEquivalence C X Y)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison_isWeakHomotopyEquivalence C Y Z))
  change AnodyneHomotopy.anodyneQ.map _ ≫ (inv (AnodyneHomotopy.anodyneQ.map _) ≫ _) = _
  exact IsIso.hom_inv_id_assoc _ _

lemma dkHammockComparison_composition (X Y Z : C.category) :
    AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComposition C X Y Z) ≫
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockColimitComparisonIso C X Z).hom =
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockProductComparisonIso C X Y Z).hom ≫
        AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition C.weakEquivalences X Y Z) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := _root_.SerrePositivity.EInfinity.Hammock.anodyneQ_map_isIso_of_weak
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C X Y ⊗ₘ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C Y Z)
    (_root_.SerrePositivity.EInfinity.Hammock.weakTensor (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison_isWeakHomotopyEquivalence C X Y)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison_isWeakHomotopyEquivalence C Y Z))
  apply (cancel_epi (Q.map
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C X Y ⊗ₘ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C Y Z))).mp
  rw [← Category.assoc, ← Q.map_comp, ← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComposition_comparison,
    Q.map_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockColimitComparisonIso_fac, ← Q.map_comp,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComposition_augmentation, Q.map_comp,
    ← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockProductComparisonIso_fac, Category.assoc]

lemma dkHammockComparisonIso_reduction (X Y : C.category) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockColimitComparisonIso C X Y).hom ≫
        AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.EInfinity.Hammock.reducedColimitIso C.weakEquivalences X Y).hom =
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockComparisonIso C X Y).hom := by
  have := _root_.SerrePositivity.EInfinity.Hammock.anodyneQ_map_isIso_of_weak (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C X Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison_isWeakHomotopyEquivalence C X Y)
  apply (cancel_epi (AnodyneHomotopy.anodyneQ.map
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C X Y))).mp
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockColimitComparisonIso_fac, ← Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockComparisonIso_fac]
  rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
