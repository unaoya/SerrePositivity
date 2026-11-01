module

public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.Presentation.RetractWords
public import SerrePositivity.CategoryTheory.Quiver.PathFunctorExt

/-!
# 中断した任意モデル源への一般化：RetractWordExt

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Extensionality on the actual generating arrows of the retract-word quotient。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0025][inventory]を参照する。

[inventory]: ../../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0025
[plan]: ../../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Extensionality on the actual generating arrows of the retract-word quotient
-/

@[expose] public section
universe u v w uD vD
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.RetractWords
variable {C : Type u} [Category.{v} C] {M : Type w} [MonoidWithZero M]
  {D : Type uD} [Category.{vD} D]

lemma functor_ext_generators (F G : Obj C M ⥤ D) (ho : ∀ X, F.obj X = G.obj X)
    (hm : ∀ {X Y : Vertex C M} (e : X ⟶ Y),
      HEq (F.map ((quotient C M).map ((Paths.of _).map e)))
        (G.map ((quotient C M).map ((Paths.of _).map e)))) : F = G := by
  apply CategoryTheory.Quotient.lift_unique' (Rel C M)
  apply QuiverPaths.functor_ext_edges
  · intro X
    exact ho ((quotient C M).obj X)
  · intro X Y e
    exact hm e

end SerrePositivity.RetractWords
