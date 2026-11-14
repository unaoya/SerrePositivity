module

public import SerrePositivity.EInfinity.Hammock.MiddleBackwardPositions
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendArrowProperty

/-!
# 中央の実際の列とブロック図式の中央の脚の性質

概要：中央の元の列の任意の射の性質は、同じ図式の中央の自然な脚の性質と同値。
方針：連結の同じ元の左列・右列の移送を二度消す。
規約：中央の自明性を、別の代表の性質で置き換えない。
使われ方：実際の固定語の全部分圏への左置換の着地。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyColumnProperty
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C] [ModelCategory C]
  {n m : ℕ} {X Y : C} (F : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family D C n m X Y)

lemma middleColumn_property (P : MorphismProperty C) (d : D) :
    P ((F.zigzagFunctor.obj d).arrow (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.middleColumn n m)) ↔ P (F.middle.app d) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyFunctor.zigzagFunctor, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family.zigzagObj, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.obj, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryBlock,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryBlock, _root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.middleColumn]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_left_property P, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_right_property P]
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyColumnProperty (middleColumn_property)


end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyColumnProperty
