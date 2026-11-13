module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ThreeArrowPaddingVertices
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordEmbeddingObjects
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn

/-!
# 元の WordAction の二配置の全列の回収

概要：元の二つの包含の WordAction は、明示的な外側・内側の配置そのものである。
方針：像の列は元の同じ射、像の外の列は元の恒等列として回収する。
規約：全頂点と全列の射を照合した元の zigzag の等式を提供する。
使われ方：配置間の自然変換を元の graph の比較に移す。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] {X Y : C}

lemma identityColumn_arrow_heq_id {R : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects.word X Y}
    {j : Fin 5} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn R j) {Z : C} (hs : R.vertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects.word.source j) = Z) :
    HEq (R.arrow j) (𝟙 Z) := by
  rw [h.arrow_eq]
  apply (eqToHom_heq_id_dom _ _ _).trans
  cases hs
  rfl

lemma outer_action_arrows (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y) (j : Fin 5) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.outerWordMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.obj S)).arrow j) ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects.outer S).arrow j) := by
  fin_cases j
  · have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.arrow_image_heq _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.outerWordMap _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.outerWordMap_injective
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.obj S) (0 : Fin 3)
    rw [congrFun _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.outerWordMap_columns (0 : Fin 3)] at he
    exact he
  · apply _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.identityColumn_arrow_heq_id
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.identityOutside_obj
      intro i
      rw [congrFun _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.outerWordMap_columns i]
      fin_cases i <;> decide
    · exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.outer_action_vertices S (2 : Fin 6)
  · have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.arrow_image_heq _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.outerWordMap _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.outerWordMap_injective
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.obj S) (1 : Fin 3)
    rw [congrFun _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.outerWordMap_columns (1 : Fin 3)] at he
    exact he
  · apply _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.identityColumn_arrow_heq_id
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.identityOutside_obj
      intro i
      rw [congrFun _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.outerWordMap_columns i]
      fin_cases i <;> decide
    · exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.outer_action_vertices S (4 : Fin 6)
  · have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.arrow_image_heq _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.outerWordMap _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.outerWordMap_injective
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.obj S) (2 : Fin 3)
    rw [congrFun _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.outerWordMap_columns (2 : Fin 3)] at he
    exact he

lemma inner_action_arrows (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y) (j : Fin 5) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.innerWordMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.obj S)).arrow j) ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects.inner S).arrow j) := by
  fin_cases j
  · apply _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.identityColumn_arrow_heq_id
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.identityOutside_obj
      intro i
      rw [congrFun _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.innerWordMap_columns i]
      fin_cases i <;> decide
    · exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.inner_action_vertices S (1 : Fin 6)
  · have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.arrow_image_heq _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.innerWordMap _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.innerWordMap_injective
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.obj S) (0 : Fin 3)
    rw [congrFun _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.innerWordMap_columns (0 : Fin 3)] at he
    exact he
  · have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.arrow_image_heq _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.innerWordMap _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.innerWordMap_injective
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.obj S) (1 : Fin 3)
    rw [congrFun _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.innerWordMap_columns (1 : Fin 3)] at he
    exact he
  · have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.arrow_image_heq _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.innerWordMap _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.innerWordMap_injective
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.obj S) (2 : Fin 3)
    rw [congrFun _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.innerWordMap_columns (2 : Fin 3)] at he
    exact he
  · apply _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.identityColumn_arrow_heq_id
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.identityOutside_obj
      intro i
      rw [congrFun _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.innerWordMap_columns i]
      fin_cases i <;> decide
    · exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.inner_action_vertices S (5 : Fin 6)

lemma outer_action_obj (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.outerWordMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.obj S) = _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects.outer S :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext _ _ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.outer_action_vertices S) (outer_action_arrows S)

lemma inner_action_obj (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.innerWordMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.obj S) = _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects.inner S :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext _ _ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.inner_action_vertices S) (inner_action_arrows S)

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
