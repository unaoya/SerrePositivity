module

public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.Presentation.AmbientWords

/-!
# 中断した任意モデル源への一般化：AmbientWordAugmentation

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual augmentation forgets all ambient word actions。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0018][inventory]を参照する。

[inventory]: ../../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0018
[plan]: ../../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual augmentation forgets all ambient word actions
-/

@[expose] public section
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.AmbientWords
variable (C : Type u) [Category.{v} C] (M : Type w) [Monoid M]

def augmentationRealization : Realization C M C where
  ambient := 𝟭 C
  action X _ := 𝟙 X
  action_one _ := rfl
  action_mul _ _ _ := (Category.id_comp _).symm

def augmentation : Obj C M ⥤ C := (augmentationRealization C M).functor

lemma augmentation_source {X Y : C} (f : X ⟶ Y) :
    (augmentation C M).map ((sourceFunctor C M).map f) = f :=
  (augmentationRealization C M).functor_source f

lemma augmentation_word (X : C) (t : M) :
    (augmentation C M).map ((quotient C M).map (word C M X t)) = 𝟙 X :=
  (augmentationRealization C M).functor_word X t

end SerrePositivity.AmbientWords
