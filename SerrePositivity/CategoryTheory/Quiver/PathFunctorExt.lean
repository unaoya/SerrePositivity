module

public import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# 自由な道の圏からの関手は対象と生成辺上の値で決まる

## 概要
自由な道の圏からの関手は対象と生成辺上の値で決まる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
生成辺と空の道を指定し、道の長さに関する帰納で射を比較する。
連結との交換から関手または自然変換の法則を確認する。

## 規約と注意
圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
表示された圏や比較射を、局所化後の同型だけで置き換えない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。
[棚卸し m0033][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0033
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Functors out of a path category are determined by vertices and generating edges
-/

@[expose] public section
universe u v uD vD
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.QuiverPaths
variable {V : Type u} [Quiver.{v} V] {D : Type uD} [Category.{vD} D]

lemma prefunctor_hext {F G : V ⥤q D} (ho : ∀ X, F.obj X = G.obj X)
    (hm : ∀ {X Y : V} (e : X ⟶ Y), HEq (F.map e) (G.map e)) : F = G := by
  cases F with
  | mk fo fm =>
    cases G with
    | mk go gm =>
      have he : fo = go := funext ho
      subst go
      congr 1
      funext X Y e
      exact eq_of_heq (hm e)

/-- 自由な道の圏からの関手は対象と生成辺上の値で決まる。

圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
生成辺と空の道を指定し、道の長さに関する帰納で射を比較する。
連結との交換から関手または自然変換の法則を確認する。
-/
lemma functor_ext_edges (F G : Paths V ⥤ D) (ho : ∀ X, F.obj X = G.obj X)
    (hm : ∀ {X Y : V} (e : X ⟶ Y),
      HEq (F.map ((Paths.of V).map e)) (G.map ((Paths.of V).map e))) : F = G := by
  have he : Paths.of V ⋙q F.toPrefunctor = Paths.of V ⋙q G.toPrefunctor :=
    prefunctor_hext ho (fun e => hm e)
  exact (Paths.lift_unique _ F he).trans (Paths.lift_unique _ G rfl).symm

end SerrePositivity.QuiverPaths
