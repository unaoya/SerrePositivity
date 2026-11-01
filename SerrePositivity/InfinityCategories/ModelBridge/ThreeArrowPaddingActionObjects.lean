module

public import SerrePositivity.InfinityCategories.ModelBridge.ThreeArrowPaddingVertices
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordEmbeddingObjects
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.IdentityColumn

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
namespace SerrePositivity.EInfinity.Hammock.ThreeArrow.Padding
open CategoryTheory HomotopicalAlgebra FrameHom

variable {C : Type u} [Category.{v} C] [ModelCategory C] {X Y : C}

lemma identityColumn_arrow_heq_id {R : Zigzag (weakEquivalences C) word X Y}
    {j : Fin 5} (h : IdentityColumn R j) {Z : C} (hs : R.vertex (word.source j) = Z) :
    HEq (R.arrow j) (𝟙 Z) := by
  rw [h.arrow_eq]
  apply (eqToHom_heq_id_dom _ _ _).trans
  cases hs
  rfl

lemma outer_action_arrows (S : WeakThreeArrow X Y) (j : Fin 5) :
    HEq ((WordAction.obj outerWordMap (ThreeArrow.obj S)).arrow j) ((outer S).arrow j) := by
  fin_cases j
  · have he := WordAction.arrow_image_heq outerWordMap outerWordMap_injective
      (ThreeArrow.obj S) (0 : Fin 3)
    rw [congrFun outerWordMap_columns (0 : Fin 3)] at he
    exact he
  · apply identityColumn_arrow_heq_id
    · apply WordAction.identityOutside_obj
      intro i
      rw [congrFun outerWordMap_columns i]
      fin_cases i <;> decide
    · exact outer_action_vertices S (2 : Fin 6)
  · have he := WordAction.arrow_image_heq outerWordMap outerWordMap_injective
      (ThreeArrow.obj S) (1 : Fin 3)
    rw [congrFun outerWordMap_columns (1 : Fin 3)] at he
    exact he
  · apply identityColumn_arrow_heq_id
    · apply WordAction.identityOutside_obj
      intro i
      rw [congrFun outerWordMap_columns i]
      fin_cases i <;> decide
    · exact outer_action_vertices S (4 : Fin 6)
  · have he := WordAction.arrow_image_heq outerWordMap outerWordMap_injective
      (ThreeArrow.obj S) (2 : Fin 3)
    rw [congrFun outerWordMap_columns (2 : Fin 3)] at he
    exact he

lemma inner_action_arrows (S : WeakThreeArrow X Y) (j : Fin 5) :
    HEq ((WordAction.obj innerWordMap (ThreeArrow.obj S)).arrow j) ((inner S).arrow j) := by
  fin_cases j
  · apply identityColumn_arrow_heq_id
    · apply WordAction.identityOutside_obj
      intro i
      rw [congrFun innerWordMap_columns i]
      fin_cases i <;> decide
    · exact inner_action_vertices S (1 : Fin 6)
  · have he := WordAction.arrow_image_heq innerWordMap innerWordMap_injective
      (ThreeArrow.obj S) (0 : Fin 3)
    rw [congrFun innerWordMap_columns (0 : Fin 3)] at he
    exact he
  · have he := WordAction.arrow_image_heq innerWordMap innerWordMap_injective
      (ThreeArrow.obj S) (1 : Fin 3)
    rw [congrFun innerWordMap_columns (1 : Fin 3)] at he
    exact he
  · have he := WordAction.arrow_image_heq innerWordMap innerWordMap_injective
      (ThreeArrow.obj S) (2 : Fin 3)
    rw [congrFun innerWordMap_columns (2 : Fin 3)] at he
    exact he
  · apply identityColumn_arrow_heq_id
    · apply WordAction.identityOutside_obj
      intro i
      rw [congrFun innerWordMap_columns i]
      fin_cases i <;> decide
    · exact inner_action_vertices S (5 : Fin 6)

lemma outer_action_obj (S : WeakThreeArrow X Y) :
    WordAction.obj outerWordMap (ThreeArrow.obj S) = outer S :=
  Zigzag.object_ext _ _ (outer_action_vertices S) (outer_action_arrows S)

lemma inner_action_obj (S : WeakThreeArrow X Y) :
    WordAction.obj innerWordMap (ThreeArrow.obj S) = inner S :=
  Zigzag.object_ext _ _ (inner_action_vertices S) (inner_action_arrows S)

end SerrePositivity.EInfinity.Hammock.ThreeArrow.Padding
