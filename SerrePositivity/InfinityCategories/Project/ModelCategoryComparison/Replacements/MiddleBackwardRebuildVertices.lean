module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.MiddleBackwardExtractFamily
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackwardPositionCases

/-!
# 元の固定語から抽出した図式の全頂点の再構成

概要：抽出した左右の射列と三つの脚を貼ると、元の全頂点を回収する。
方針：元の左右の位置の成分回収と、全頂点の場合分けを使う。
規約：両端の同定は元の first/last の等式による。
使われ方：再構成関手を元の恒等図式と同定する。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] {n m : ℕ} {X Y : C}

def rebuilt (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardExtractFamily.family.zigzagObj S

def rebuildFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y ⥤
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardExtractFamily.family.zigzagFunctor

lemma rebuilt_leftVertex (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y)
    (i : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuilt S).vertex (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.leftVertex n m i) = S.vertex (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.leftVertex n m i) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuilt, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family.zigzagObj, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardExtractFamily.family, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.obj, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryBlock,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryBlock, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.leftVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_left, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_right]
  rfl

lemma rebuilt_rightVertex (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y)
    (i : Fin (m + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuilt S).vertex (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.rightVertex n m i) = S.vertex (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.rightVertex n m i) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuilt, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family.zigzagObj, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardExtractFamily.family, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.obj, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryBlock,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryBlock, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.rightVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_right, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_left]
  rfl

lemma rebuilt_vertex (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y)
    (j : Fin ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).length + 1)) : (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuilt S).vertex j = S.vertex j := by
  apply _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.vertex_cases n m (P := fun j => (rebuilt S).vertex j = S.vertex j)
  · exact (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuilt S).first.trans S.first.symm
  · exact rebuilt_leftVertex S
  · exact rebuilt_rightVertex S
  · exact (rebuilt S).last.trans S.last.symm

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
