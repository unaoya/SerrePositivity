module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ThreeArrowPaddingWordMaps
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction

/-!
# 元の WordAction の二つの padding 配置の頂点

概要：元の二つの語の包含の作用は、外側・内側の配置と同じ全頂点を持つ。
方針：元の切断位置の有限表を同じ元の三本矢の頂点へ適用する。
規約：語の写像の単射性も元の列の表から証明する。列の射の照合は後続。
使われ方：二つの自然変換の nerve と元の比較射への接続。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory HomotopicalAlgebra

lemma outerWordMap_injective : Function.Injective _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.outerWordMap.orderHom := by
  change Function.Injective (fun i : Fin 3 => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.outerWordMap.orderHom i)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.outerWordMap_columns]
  decide

lemma innerWordMap_injective : Function.Injective _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.innerWordMap.orderHom := by
  change Function.Injective (fun i : Fin 3 => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.innerWordMap.orderHom i)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.innerWordMap_columns]
  decide

variable {C : Type u} [Category.{v} C] [ModelCategory C] {X Y : C}

lemma outer_action_vertices (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y) (j : Fin 6) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.outerWordMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.obj S)).vertex j = (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects.outer S).vertex j := by
  change (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.obj S).vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.outerWordMap.cut j) = _
  rw [congrFun _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.outerWordMap_cut j]
  fin_cases j <;> rfl

lemma inner_action_vertices (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y) (j : Fin 6) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.innerWordMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.obj S)).vertex j = (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects.inner S).vertex j := by
  change (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.obj S).vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.innerWordMap.cut j) = _
  rw [congrFun _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.innerWordMap_cut j]
  fin_cases j <;> rfl

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
