module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingActionObjects
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingMaps

/-!
# 元の WordAction と二つの padding 配置の関手の一致

概要：外側・内側の元の語の作用は、明示的な配置関手と全対象・全縦射で一致する。
方針：対象の等式に続き、元の切断位置での全縦射を比較する。
規約：関手の異種等式による外延性を用い、自然同型だけで代用しない。
使われ方：二つの配置の nerve ホモトピーを元の比較射へ移す。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] {X Y : C}

lemma outer_action_functor : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.functor (X := X) (Y := Y) ⋙
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.outerWordMap = _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.outerFunctor := by
  apply Functor.hext (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.outer_action_obj)
  intro S T f
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.outer_action_obj S) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.outer_action_obj T)
  intro j
  change HEq ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.map f).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.outerWordMap.cut j)) ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.outerMap f).app j)
  rw [congrFun _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.outerWordMap_cut j]
  change Fin 6 at j
  fin_cases j <;> rfl

lemma inner_action_functor : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.functor (X := X) (Y := Y) ⋙
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.innerWordMap = _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.innerFunctor := by
  apply Functor.hext (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.inner_action_obj)
  intro S T f
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.inner_action_obj S) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.inner_action_obj T)
  intro j
  change HEq ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.map f).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.innerWordMap.cut j)) ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.innerMap f).app j)
  rw [congrFun _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.innerWordMap_cut j]
  change Fin 6 at j
  fin_cases j <;> rfl

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
