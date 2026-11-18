module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockPrecompose

/-!
# 元の射に沿う DK hammock 比較の両端点自然性

概要：元の射の点による前後合成を anodyne 局所化内の同じ比較が保つ。
方針：共通始域の左右の正方形を送り、元の右弱比較を消去する。
規約：原圏上の生の DK Hom の厳密な双関手は仮定しない。
使われ方：既存 Map^h の高次比較の両端点自然性。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock _root_.SerrePositivity.InfinityCategories _root_.SerrePositivity.SimplicialModel
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

lemma dkHammockColimitComparisonIso_postcompose (X : C.category) {Y Z : C.category}
    (g : Y ⟶ Z) :
    AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationPostcompose C X g) ≫
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockColimitComparisonIso C X Z).hom =
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockColimitComparisonIso C X Y).hom ≫
        AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap X (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences g)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.anodyneQ_map_isIso_of_weak (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C X Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison_isWeakHomotopyEquivalence C X Y)
  have hr := congrArg Q.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockPostcompose_comparison C X g)
  have hl := congrArg Q.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockPostcompose_augmentation C X g)
  simp only [Functor.map_comp] at hr hl
  apply (cancel_epi (Q.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C X Y))).mp
  rw [← Category.assoc, ← hr, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockColimitComparisonIso_fac, hl,
    ← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockColimitComparisonIso_fac, Category.assoc]

lemma dkHammockColimitComparisonIso_precompose {X Y : C.category} (Z : C.category)
    (f : X ⟶ Y) :
    AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationPrecompose C Z f) ≫
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockColimitComparisonIso C X Z).hom =
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockColimitComparisonIso C Y Z).hom ≫
        AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences f) Z) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.anodyneQ_map_isIso_of_weak (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C Y Z)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison_isWeakHomotopyEquivalence C Y Z)
  have hr := congrArg Q.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockPrecompose_comparison C Z f)
  have hl := congrArg Q.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockPrecompose_augmentation C Z f)
  simp only [Functor.map_comp] at hr hl
  apply (cancel_epi (Q.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C Y Z))).mp
  rw [← Category.assoc, ← hr, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockColimitComparisonIso_fac, hl,
    ← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockColimitComparisonIso_fac, Category.assoc]

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
