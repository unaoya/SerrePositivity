module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.MiddleBackwardContextRightReplacement
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumnOfHEq

/-!
# 任意の前後の語の中の右置換の中央恒等列

概要：元の全体の右置換の中央列は、元の対象と射の意味で恒等列となる。
方針：連結の両端と全列の回収を繰り返し、中央の元の恒等射へ戻す。
規約：前後の語と動く接合対象を保持する。
使われ方：元の eraseInclusion の実際の対象の像の回収。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (n m : ℕ) (X Y : C)

lemma rightReplacement_identity (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextTrivialCofibration.Objects a b n m X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextRightReplacement.rightReplacement a b n m X Y).obj S) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.middleColumn a b n m) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn.of_heq_id (E := ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextRightReplacement.sourceFamily a b n m X Y).left.obj S).obj (Fin.last n))
  all_goals
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextRightReplacement.rightReplacement, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextRightReplacement.rightDiagram, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramFixed.fixedFunctor,
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramAppend.append, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyPushout.pushoutDiagram, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily.zigzagObj,
      _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.obj, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyPushout.pushoutFamily, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyPushout.pushoutMiddle, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.middleColumn]
  · apply Eq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.source_left_eq _ _ _)
    apply Eq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.source_right_eq _ _ _)
    dsimp only [_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.middleColumn]
    apply Eq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.source_left_eq _ _ _)
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.source_right_eq _ _ _
  · apply Eq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.target_left_eq _ _ _)
    apply Eq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.target_right_eq _ _ _)
    dsimp only [_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.middleColumn]
    apply Eq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.target_left_eq _ _ _)
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.target_right_eq _ _ _
  · apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq _ _ _)
    apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_right_heq _ _ _)
    dsimp only [_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.middleColumn]
    apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq _ _ _)
    apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_right_heq _ _ _)
    rfl

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
