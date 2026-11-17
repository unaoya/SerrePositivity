module

public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnMixedRightIso

/-!
# 元の混合二方向の右係数積の弱比較

概要：元の右比較射を通常 Hom と残りの語の同じ比較射の積へ回収する。
方針：元の全射列の射影・組み立ての同型と augmentation の正方形を使う。
規約：残りの元の語の比較だけを帰納仮定にする。
使われ方：DK5.7の混合二方向の帰納段階。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory MonoidalCategory _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization SerrePositivity.InfinityCategories
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y Z : C.category)
lemma freeMixedFirstRightSpaceMap_weak
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation C Z Y).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (freeMixedFirstRightSpaceMap C w X Y Z) := by
  have hp := weakTensor (freeFirstRightSpaceMap_weak C w X Y Z)
    (freeBackwardFirstRightSpaceMap_weak C w X Y Z h)
  have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (freeMixedFirstRightSpaceIso C w X Y Z)).isWeakHomotopyEquivalence.comp hp
  rw [← freeMixedFirstRightSpaceIso_augmentation] at hc
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (freeMixedFirstTargetRightSpaceIso C w X Y Z)).isWeakHomotopyEquivalence.cancel_right hc
end SerrePositivity.EInfinity.Hammock.FirstColumn
