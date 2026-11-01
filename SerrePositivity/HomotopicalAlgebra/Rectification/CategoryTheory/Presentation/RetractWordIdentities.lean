module

public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.Presentation.RetractWords

/-!
# 中断した任意モデル源への一般化：RetractWordIdentities

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The defining retract relations as equalities of actual quotient arrows。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0026][inventory]を参照する。

[inventory]: ../../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0026
[plan]: ../../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The defining retract relations as equalities of actual quotient arrows
-/

@[expose] public section
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.RetractWords
variable (C : Type u) [Category.{v} C] (M : Type w) [MonoidWithZero M]

lemma quotient_word_one (X : C) : (quotient C M).map (word C M X 1) = 𝟙 _ := by
  simpa using CategoryTheory.Quotient.sound (Rel C M) (Rel.word_one X)

lemma quotient_word_zero (X : C) :
    (quotient C M).map (word C M X 0) =
      (quotient C M).map (projection C M X) ≫ (quotient C M).map (section_ C M X) := by
  simpa using CategoryTheory.Quotient.sound (Rel C M) (Rel.word_zero X)

lemma quotient_split (X : C) :
    (quotient C M).map (section_ C M X) ≫ (quotient C M).map (projection C M X) = 𝟙 _ := by
  simpa using CategoryTheory.Quotient.sound (Rel C M) (Rel.split X)

end SerrePositivity.RetractWords
