module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ThreeArrowPaddingWordMaps
public import SerrePositivity.InfinityCategories.ModelBridge.ThreeArrowPaddingObjects
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordAction

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
namespace SerrePositivity.EInfinity.Hammock.ThreeArrow.Padding
open CategoryTheory HomotopicalAlgebra FrameHom

lemma outerWordMap_injective : Function.Injective outerWordMap.orderHom := by
  change Function.Injective (fun i : Fin 3 => outerWordMap.orderHom i)
  rw [outerWordMap_columns]
  decide

lemma innerWordMap_injective : Function.Injective innerWordMap.orderHom := by
  change Function.Injective (fun i : Fin 3 => innerWordMap.orderHom i)
  rw [innerWordMap_columns]
  decide

variable {C : Type u} [Category.{v} C] [ModelCategory C] {X Y : C}

lemma outer_action_vertices (S : WeakThreeArrow X Y) (j : Fin 6) :
    (WordAction.obj outerWordMap (ThreeArrow.obj S)).vertex j = (outer S).vertex j := by
  change (ThreeArrow.obj S).vertex (outerWordMap.cut j) = _
  rw [congrFun outerWordMap_cut j]
  fin_cases j <;> rfl

lemma inner_action_vertices (S : WeakThreeArrow X Y) (j : Fin 6) :
    (WordAction.obj innerWordMap (ThreeArrow.obj S)).vertex j = (inner S).vertex j := by
  change (ThreeArrow.obj S).vertex (innerWordMap.cut j) = _
  rw [congrFun innerWordMap_cut j]
  fin_cases j <;> rfl

end SerrePositivity.EInfinity.Hammock.ThreeArrow.Padding
