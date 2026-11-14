module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.MiddleBackwardMovingFamilyDiagram
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.MiddleBackwardFamilyColumnProperty

/-!
# 動く端点を持つ図式の中央列の性質

概要：元の中央列の性質を、同じ MovingFamily の中央の脚から回収する。
方針：同じ列に沿う連結の二度の等式移送を消去する。
規約：端点が添字とともに動いても、実際の中央の列を使用する。
使われ方：任意の前後の語を保持した左置換の自明性の証明。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyColumnProperty
open CategoryTheory HomotopicalAlgebra

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C] [ModelCategory C]
  {n m : ℕ} {A B : D ⥤ C} (F : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily D C n m A B)

lemma middleColumn_property (P : MorphismProperty C) (d : D) :
    P ((F.zigzagObj d).arrow (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.middleColumn n m)) ↔ P (F.middle.app d) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily.zigzagObj, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.obj, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryBlock,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryBlock, _root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.middleColumn]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_left_property P, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_right_property P]
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyColumnProperty (middleColumn_property)


end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyColumnProperty
