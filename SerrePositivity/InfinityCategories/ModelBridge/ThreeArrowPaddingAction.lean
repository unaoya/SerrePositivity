module

public import SerrePositivity.InfinityCategories.ModelBridge.ThreeArrowPaddingActionObjects
public import SerrePositivity.InfinityCategories.ModelBridge.ThreeArrowPaddingMaps

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
namespace SerrePositivity.EInfinity.Hammock.ThreeArrow.Padding
open CategoryTheory HomotopicalAlgebra FrameHom

variable {C : Type u} [Category.{v} C] [ModelCategory C] {X Y : C}

lemma outer_action_functor : ThreeArrow.functor (X := X) (Y := Y) ⋙
    WordAction.functor outerWordMap = outerFunctor := by
  apply Functor.hext (outer_action_obj)
  intro S T f
  apply Zigzag.hom_hext (outer_action_obj S) (outer_action_obj T)
  intro j
  change HEq ((ThreeArrow.map f).app (outerWordMap.cut j)) ((outerMap f).app j)
  rw [congrFun outerWordMap_cut j]
  change Fin 6 at j
  fin_cases j <;> rfl

lemma inner_action_functor : ThreeArrow.functor (X := X) (Y := Y) ⋙
    WordAction.functor innerWordMap = innerFunctor := by
  apply Functor.hext (inner_action_obj)
  intro S T f
  apply Zigzag.hom_hext (inner_action_obj S) (inner_action_obj T)
  intro j
  change HEq ((ThreeArrow.map f).app (innerWordMap.cut j)) ((innerMap f).app j)
  rw [congrFun innerWordMap_cut j]
  change Fin 6 at j
  fin_cases j <;> rfl

end SerrePositivity.EInfinity.Hammock.ThreeArrow.Padding
