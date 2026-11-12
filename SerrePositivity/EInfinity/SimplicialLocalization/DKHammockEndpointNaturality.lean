module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockPrecompose

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
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Hammock SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

lemma dkHammockColimitComparisonIso_postcompose (X : C.category) {Y Z : C.category}
    (g : Y ⟶ Z) :
    AnodyneHomotopy.anodyneQ.map (localizationPostcompose C X g) ≫
        (dkHammockColimitComparisonIso C X Z).hom =
      (dkHammockColimitComparisonIso C X Y).hom ≫
        AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap X (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences g)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := anodyneQ_map_isIso_of_weak (freeHammockDiagonalComparison C X Y)
    (freeHammockDiagonalComparison_isWeakHomotopyEquivalence C X Y)
  have hr := congrArg Q.map (freeHammockPostcompose_comparison C X g)
  have hl := congrArg Q.map (freeHammockPostcompose_augmentation C X g)
  simp only [Functor.map_comp] at hr hl
  apply (cancel_epi (Q.map (freeHammockDiagonalComparison C X Y))).mp
  rw [← Category.assoc, ← hr, Category.assoc, dkHammockColimitComparisonIso_fac, hl,
    ← dkHammockColimitComparisonIso_fac, Category.assoc]

lemma dkHammockColimitComparisonIso_precompose {X Y : C.category} (Z : C.category)
    (f : X ⟶ Y) :
    AnodyneHomotopy.anodyneQ.map (localizationPrecompose C Z f) ≫
        (dkHammockColimitComparisonIso C X Z).hom =
      (dkHammockColimitComparisonIso C Y Z).hom ≫
        AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences f) Z) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := anodyneQ_map_isIso_of_weak (freeHammockDiagonalComparison C Y Z)
    (freeHammockDiagonalComparison_isWeakHomotopyEquivalence C Y Z)
  have hr := congrArg Q.map (freeHammockPrecompose_comparison C Z f)
  have hl := congrArg Q.map (freeHammockPrecompose_augmentation C Z f)
  simp only [Functor.map_comp] at hr hl
  apply (cancel_epi (Q.map (freeHammockDiagonalComparison C Y Z))).mp
  rw [← Category.assoc, ← hr, Category.assoc, dkHammockColimitComparisonIso_fac, hl,
    ← dkHammockColimitComparisonIso_fac, Category.assoc]

end SerrePositivity.EInfinity.SimplicialLocalization
