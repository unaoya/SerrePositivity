module

public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnMixedPointWeak
public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnMixedRightWeak
public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramSimplicialWeak
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordSingleCons

/-!
# 元の自由対角比較の混合二方向 +−の帰納段階

概要：残りの語の元の比較が弱同値なら、前向きの先頭列を加えた元の比較も弱同値。
方針：元の右係数の回収と底・一点係数 の具体的な弱同値性を二方向対角定理へ渡す。
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
variable (C : RelativeCategory.{u}) (w : Word) (X Y : C.category)
lemma freeWordDiagonalAugmentation_forwardBackward_weak
    (hTail : ∀ Z : C.category, IsWeakHomotopyEquivalence
      ((freeWordDiagonalAugmentation C Z Y).app (Word.cons .backward w))) :
    IsWeakHomotopyEquivalence ((freeWordDiagonalAugmentation C X Y).app
      (Word.append (Word.single .forward) (Word.cons .backward w))) := by
  apply (forwardBackwardDiagonalAugmentation_weak_iff C w X Y (freeResolution C)
    (freeResolutionObject C) (fun θ X => freeResolutionObject_naturality C θ X)
    (freeResolutionAugmentationNatTrans C) (freeResolutionObject_augmentation C)).mpr
  exact TwoSidedDiagram.FixedVertices.diagonalTotalMap_weak
    (D := freeForwardBackwardDiagram C w X Y)
    (E := (Functor.const SimplexCategoryᵒᵖ).obj (forwardBackwardData C w X Y))
    (freeFirstMarkedObjectEquiv C) (freeMixedFirstTargetObjectEquiv C w X Y)
    (freeMixedFirstMarkedObjectEquiv_naturality C w X Y)
    (freeMixedFirstTargetObjectEquiv_naturality C w X Y)
    (freeForwardBackwardAugmentation C w X Y)
    (freeMixedFirstMarkedObjectEquiv_augmentation C w X Y)
    (freeMixedFirstHomSpaceMap_weak C w X Y)
    (freeMixedFirstLeftSpaceMap_weak C w X Y)
    (fun Z => freeMixedFirstRightSpaceMap_weak C w X Y Z (hTail Z))
lemma freeWordDiagonalAugmentation_cons_forwardBackward_weak
    (hTail : ∀ Z : C.category, IsWeakHomotopyEquivalence
      ((freeWordDiagonalAugmentation C Z Y).app (Word.cons .backward w))) :
    IsWeakHomotopyEquivalence ((freeWordDiagonalAugmentation C X Y).app
      (Word.cons .forward (Word.cons .backward w))) := by
  exact Eq.mp (congrArg (fun a : Word => IsWeakHomotopyEquivalence
    ((freeWordDiagonalAugmentation C X Y).app a))
      (Word.single_append_eq_cons .forward (Word.cons .backward w)))
        (freeWordDiagonalAugmentation_forwardBackward_weak C w X Y hTail)

lemma freeWordDiagonalAugmentation_twoForwardBackward_weak :
    IsWeakHomotopyEquivalence ((freeWordDiagonalAugmentation C X Y).app
      (Word.cons .forward (Word.single .backward))) := by
  have hTail : ∀ Z : C.category, IsWeakHomotopyEquivalence
      ((freeWordDiagonalAugmentation C Z Y).app (Word.cons .backward Word.empty)) := by
    intro Z
    exact Eq.mpr (congrArg (fun a : Word => IsWeakHomotopyEquivalence
      ((freeWordDiagonalAugmentation C Z Y).app a)) (Word.cons_empty .backward))
        (freeWordDiagonalAugmentation_backward_weak C Z Y)
  exact Eq.mp (congrArg (fun a : Word => IsWeakHomotopyEquivalence
    ((freeWordDiagonalAugmentation C X Y).app a))
      (congrArg (Word.cons .forward) (Word.cons_empty .backward)))
        (freeWordDiagonalAugmentation_cons_forwardBackward_weak C Word.empty X Y hTail)
end SerrePositivity.EInfinity.SimplicialLocalization
