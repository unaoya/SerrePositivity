module

public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnLeftWeak
public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnRightWeak
public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramSimplicialWeak
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordSingleCons

/-!
# 元の自由対角比較の前向き二列の帰納段階

概要：残りの語の元の比較が弱同値なら、前向きの先頭列を加えた元の比較も弱同値。
方針：元の左係数の回収と底・右 Hom の具体的な弱同値性を二方向対角定理へ渡す。
規約：底と右の弱同値性を入力せず、同じ元の Word 対角射を結論する。
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
lemma freeWordDiagonalAugmentation_forwardForward_weak
    (hTail : ∀ Z : C.category, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation C Z Y).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation C X Y).app
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w))) := by
  apply (forwardForwardDiagonalAugmentation_weak_iff C w X Y (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C) (fun θ X => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_naturality C θ X)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C)).mpr
  exact TwoSidedDiagram.FixedVertices.diagonalTotalMap_weak
    (D := freeForwardForwardDiagram C w X Y)
    (E := (Functor.const SimplexCategoryᵒᵖ).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardData C w X Y))
    (freeFirstMarkedObjectEquiv C) (freeFirstTargetObjectEquiv C w X Y)
    (freeFirstMarkedObjectEquiv_naturality C w X Y)
    (freeFirstTargetObjectEquiv_naturality C w X Y) (freeForwardForwardAugmentation C w X Y)
    (freeFirstMarkedObjectEquiv_augmentation C w X Y) (freeFirstHomSpaceMap_weak C w X Y)
    (fun Z => freeFirstLeftSpaceMap_weak C w X Y Z (hTail Z)) (freeFirstRightSpaceMap_weak C w X Y)
lemma freeWordDiagonalAugmentation_cons_forwardForward_weak
    (hTail : ∀ Z : C.category, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation C Z Y).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation C X Y).app
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w))) := by
  exact Eq.mp (congrArg (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation C X Y).app a))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.single_append_eq_cons .forward (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w)))
        (freeWordDiagonalAugmentation_forwardForward_weak C w X Y hTail)

lemma freeWordDiagonalAugmentation_twoForward_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation C X Y).app
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward))) := by
  have hTail : ∀ Z : C.category, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation C Z Y).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty)) := by
    intro Z
    exact Eq.mpr (congrArg (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation C Z Y).app a)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons_empty .forward))
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation_forward_weak C Z Y)
  exact Eq.mp (congrArg (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation C X Y).app a))
      (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons_empty .forward)))
        (freeWordDiagonalAugmentation_cons_forwardForward_weak C _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty X Y hTail)
end SerrePositivity.EInfinity.SimplicialLocalization
