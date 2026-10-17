module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.ParameterComposition

/-!
# 中断した任意モデル源への一般化：ParameterCategory

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類C）。
対象：Categories of maps with a shared arbitrary simplicial parameter。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0507][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0507
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Categories of maps with a shared arbitrary simplicial parameter
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.ParameterCategory

structure Object (T : SSet.{v}) where
  value : SSet.{v}

instance (T : SSet.{v}) : Category.{v} (Object T) where
  Hom X Y := X.value ⊗ T ⟶ Y.value
  id X := ParameterComposition.const T (𝟙 X.value)
  comp f g := ParameterComposition.comp f g
  id_comp := ParameterComposition.id_comp
  comp_id := ParameterComposition.comp_id
  assoc := ParameterComposition.assoc

def reindex {T U : SSet.{v}} (j : U ⟶ T) : Object T ⥤ Object U where
  obj X := ⟨X.value⟩
  map f := ParameterComposition.substitute j f
  map_id _ := ParameterComposition.substitute_const j _
  map_comp f g := ParameterComposition.substitute_comp j f g

lemma reindex_id (T : SSet.{v}) : reindex (𝟙 T) = 𝟭 (Object T) := by
  apply CategoryTheory.Functor.ext (fun _ => rfl)

lemma reindex_comp {T U V : SSet.{v}} (j : U ⟶ T) (k : V ⟶ U) :
    reindex (k ≫ j) = reindex j ⋙ reindex k := by
  apply CategoryTheory.Functor.ext (fun _ => rfl)

end SerrePositivity.SimplicialModel.ParameterCategory
