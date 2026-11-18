module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.MiddleBackwardMovingExtractRecovery
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramExt

/-!
# 動く局所図式の全縦射と図式自体の回収

概要：元の図式から抽出したブロックの貼り直しは、元の図式に厳密に等しい。
方針：左右の全縦成分と両端の元の射を回収し、図式の外延性を使う。
規約：端点の射は非恒等射でもよい。長さ零も含む。
使われ方：局所置換の counit を元の全図式へ戻す。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingExtractMapRecovery
open CategoryTheory HomotopicalAlgebra

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C] [ModelCategory C]
  {n m : ℕ} {A B : D ⥤ C}
  (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) A B)
  {d d' : D} (f : d ⟶ d')

lemma rebuilt_map_left (i : Fin (n + 1)) :
    HEq (((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingExtractFamily.family F).zigzagMap f).app (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.leftVertex n m i))
      ((F.map f).app (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.leftVertex n m i)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyMaps.zigzagMap, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyMaps.zigzagMapData, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.leftVertex]
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq (b := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord m) _ _ _)
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq (b := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) _ _ _)
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map]
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_right_heq (a := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)
    (b := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.forwardWord n) _ _ HEq.rfl i)
  rfl

lemma rebuilt_map_right (i : Fin (m + 1)) :
    HEq (((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingExtractFamily.family F).zigzagMap f).app (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.rightVertex n m i))
      ((F.map f).app (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.rightVertex n m i)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyMaps.zigzagMap, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyMaps.zigzagMapData, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.rightVertex]
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_right_heq
    (a := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.leftWithMiddle n) (b := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord m) _ _ ?_
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.forwardWord m) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) i))
  · dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map]
    apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq (a := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.forwardWord m)
      (b := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) _ _ i)
    rfl
  · apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_right_heq (b := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)
      _ _ ?_ (Fin.last 1))
    · exact (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryComparison_first (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.MovingExtract.rightPathMap (F.map f))
        (fun i => (F.map f).app_mem _) ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingExtractFamily.rightLeg F).app d) ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingExtractFamily.rightLeg F).app d')
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingExtractFamily.rightLeg_mem F d) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingExtractFamily.rightLeg_mem F d') (B.map f) (F.endpoint_right_mem f)
        ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingExtractFamily.rightLeg F).naturality f).symm).symm
    · exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryComparison_last _ _ _ _ _ _ _ _ _

lemma rebuilt_map_app (j : Fin ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).length + 1)) :
    HEq (((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingExtractFamily.family F).zigzagMap f).app j) ((F.map f).app j) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.vertex_cases n m
    (P := fun j => HEq (((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingExtractFamily.family F).zigzagMap f).app j) ((F.map f).app j))
  · exact ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingExtractFamily.family F).zigzagMap_first f).trans (F.first f).symm
  · exact rebuilt_map_left F f
  · exact rebuilt_map_right F f
  · exact ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingExtractFamily.family F).zigzagMap_last f).trans (F.last f).symm

lemma rebuildDiagram_eq : (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingExtractFamily.family F).movingDiagram = F :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ext _ _ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingExtractRecovery.rebuilt_eq F) (rebuilt_map_app F)

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingExtractMapRecovery
