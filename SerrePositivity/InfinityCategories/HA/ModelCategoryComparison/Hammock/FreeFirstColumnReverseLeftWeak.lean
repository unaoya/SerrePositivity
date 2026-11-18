module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeFirstColumnReverseLeftIso

/-!
# 元の混合二方向の左係数積の弱比較

概要：元の左比較射をnative 指定 Hom と残りの語の同じ比較射の積へ回収する。
方針：元の全射列の射影・組み立ての同型と augmentation の正方形を使う。
規約：残りの元の語の比較だけを帰納仮定にする。
使われ方：DK5.7の混合二方向の帰納段階。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization _root_.SerrePositivity.InfinityCategories
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y Z : C.category)
lemma freeReverseFirstLeftSpaceMap_weak
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation C Z Y).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeReverseFirstLeftSpaceMap C w X Y Z) := by
  have hp := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.weakTensor (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeBackwardFirstLeftSpaceMap_weak C w X Y Z)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstLeftSpaceMap_weak C w X Y Z h)
  have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeReverseFirstLeftSpaceIso C w X Y Z)).isWeakHomotopyEquivalence.comp hp
  rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeReverseFirstLeftSpaceIso_augmentation] at hc
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeReverseFirstTargetLeftSpaceIso C w X Y Z)).isWeakHomotopyEquivalence.cancel_right hc
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn
