module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardRebuildVertices
public import SerrePositivity.EInfinity.Hammock.MiddleBackwardExtractLegRecovery

/-!
# 再構成した元の zigzag の全列の回収

概要：左右の射列と三つの脚から再構成した全列は、元の同じ全列と異種等しい。
方針：元の連結の全列の成分回収を繰り返し、抽出した各隣接射へ戻す。
規約：語の向きと順序、元の全ての射を保持する。
使われ方：再構成対象と元の対象の厳密な等式。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardRebuildArrows
open CategoryTheory HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] {n m : ℕ} {X Y : C}

lemma rebuilt_firstColumn (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuilt S).arrow (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.firstColumn n m)) (S.arrow (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.firstColumn n m)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuilt, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family.zigzagObj, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardExtractFamily.family, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.obj, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryBlock,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryBlock, _root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.firstColumn]
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq (b := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord m) _ _ _)
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq (b := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) _ _ _)
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq (b := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.forwardWord n) _ _ _)
  exact _root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Extract.leftLeg_heq S

lemma rebuilt_leftColumn (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y) (i : Fin n) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuilt S).arrow (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.leftColumn n m i))
      (S.arrow (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.leftColumn n m i)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuilt, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family.zigzagObj, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardExtractFamily.family, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.obj, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryBlock,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryBlock, _root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.leftColumn]
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq (b := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord m) _ _ _)
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq (b := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) _ _ _)
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_right_heq (a := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) _ _ _)
  exact _root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Extract.leftPath_map_succ_heq S i.val i.isLt

lemma rebuilt_middleColumn (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuilt S).arrow (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.middleColumn n m))
      (S.arrow (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.middleColumn n m)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuilt, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family.zigzagObj, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardExtractFamily.family, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.obj, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryBlock,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryBlock, _root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.middleColumn]
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq (b := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord m) _ _ _)
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_right_heq (a := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord n) _ _ _)
  exact _root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Extract.middleLeg_heq S

lemma rebuilt_rightColumn (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y) (i : Fin m) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuilt S).arrow (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.rightColumn n m i))
      (S.arrow (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.rightColumn n m i)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuilt, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family.zigzagObj, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardExtractFamily.family, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.obj, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryBlock,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryBlock, _root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.rightColumn]
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_right_heq (a := _root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.leftWithMiddle n) _ _ _)
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq (b := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) _ _ _)
  exact _root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Extract.rightPath_map_succ_heq S i.val i.isLt

lemma rebuilt_lastColumn (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuilt S).arrow (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.lastColumn n m)) (S.arrow (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.lastColumn n m)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuilt, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family.zigzagObj, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardExtractFamily.family, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.obj, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryBlock,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryBlock, _root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.lastColumn]
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_right_heq (a := _root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.leftWithMiddle n) _ _ _)
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_right_heq (a := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.forwardWord m) _ _ _)
  exact _root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Extract.rightLeg_heq S

lemma rebuilt_arrow (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y)
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).length) : HEq ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuilt S).arrow j) (S.arrow j) :=
  _root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.column_cases n m (P := fun j => HEq ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuilt S).arrow j) (S.arrow j))
    (rebuilt_firstColumn S) (rebuilt_leftColumn S)
    (rebuilt_middleColumn S) (rebuilt_rightColumn S) (rebuilt_lastColumn S) j

lemma rebuilt_eq (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y) : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuilt S = S :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext _ _ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuilt_vertex S) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardRebuildArrows.rebuilt_arrow S)

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardRebuildArrows
