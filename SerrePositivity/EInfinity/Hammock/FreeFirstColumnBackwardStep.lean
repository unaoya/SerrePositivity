module

public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnBackwardLeftWeak
public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnBackwardRightWeak
public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramSimplicialWeak
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordSingleCons

/-!
# 元の自由対角比較の後向き二列の帰納段階

概要：残りの語の元の比較が弱同値なら、後向きの先頭列を加えた元の比較も弱同値。
方針：元の右係数の回収と底・左 Hom の具体的な弱同値性を二方向対角定理へ渡す。
規約：底と左の弱同値性を入力せず、同じ元の Word 対角射を結論する。
使われ方：DK5.7の元の全語の長さ帰納。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory SerrePositivity.InfinityCategories Hammock Hammock.FirstColumn
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C.category)
lemma freeWordDiagonalAugmentation_backwardBackward_weak
    (hTail : ∀ Z : C.category, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      ((freeWordDiagonalAugmentation C Z Y).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((freeWordDiagonalAugmentation C X Y).app
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w))) := by
  apply (backwardBackwardDiagonalAugmentation_weak_iff C w X Y (freeResolution C)
    (freeResolutionObject C) (fun θ X => freeResolutionObject_naturality C θ X)
    (freeResolutionAugmentationNatTrans C) (freeResolutionObject_augmentation C)).mpr
  exact TwoSidedDiagram.FixedVertices.diagonalTotalMap_weak
    (D := freeBackwardBackwardDiagram C w X Y)
    (E := (Functor.const SimplexCategoryᵒᵖ).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardData C w X Y))
    (freeFirstMarkedObjectEquiv C) (freeBackwardFirstTargetObjectEquiv C w X Y)
    (freeBackwardFirstMarkedObjectEquiv_naturality C w X Y)
    (freeBackwardFirstTargetObjectEquiv_naturality C w X Y)
    (freeBackwardBackwardAugmentation C w X Y)
    (freeBackwardFirstMarkedObjectEquiv_augmentation C w X Y)
    (freeBackwardFirstHomSpaceMap_weak C w X Y)
    (freeBackwardFirstLeftSpaceMap_weak C w X Y)
    (fun Z => freeBackwardFirstRightSpaceMap_weak C w X Y Z (hTail Z))
lemma freeWordDiagonalAugmentation_cons_backwardBackward_weak
    (hTail : ∀ Z : C.category, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      ((freeWordDiagonalAugmentation C Z Y).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((freeWordDiagonalAugmentation C X Y).app
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w))) := by
  exact Eq.mp (congrArg (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
    ((freeWordDiagonalAugmentation C X Y).app a))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.single_append_eq_cons .backward (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w)))
        (freeWordDiagonalAugmentation_backwardBackward_weak C w X Y hTail)

lemma freeWordDiagonalAugmentation_twoBackward_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((freeWordDiagonalAugmentation C X Y).app
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward))) := by
  have hTail : ∀ Z : C.category, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      ((freeWordDiagonalAugmentation C Z Y).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty)) := by
    intro Z
    exact Eq.mpr (congrArg (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      ((freeWordDiagonalAugmentation C Z Y).app a)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons_empty .backward))
        (freeWordDiagonalAugmentation_backward_weak C Z Y)
  exact Eq.mp (congrArg (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
    ((freeWordDiagonalAugmentation C X Y).app a))
      (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons_empty .backward)))
        (freeWordDiagonalAugmentation_cons_backwardBackward_weak C _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty X Y hTail)
end SerrePositivity.EInfinity.SimplicialLocalization
