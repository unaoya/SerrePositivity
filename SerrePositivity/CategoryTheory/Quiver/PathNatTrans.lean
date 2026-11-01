module

public import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# 生成辺上の自然性から道の圏上の自然変換を構成する

## 概要
生成辺上の自然性から道の圏上の自然変換を構成する。
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
[棚卸し m0035][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0035
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Natural transformations on a path category from the generator equations
-/

@[expose] public section
universe u v uD vD
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.QuiverPaths
variable {V : Type u} [Quiver.{v} V] {D : Type uD} [Category.{vD} D]

/-- 生成辺上の自然性から道の圏上の自然変換を構成する。

圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
生成辺と空の道を指定し、道の長さに関する帰納で射を比較する。
連結との交換から関手または自然変換の法則を確認する。
-/
def natTransOfEdges (F G : Paths V ⥤ D) (a : ∀ X, F.obj X ⟶ G.obj X)
    (ha : ∀ {X Y : V} (e : X ⟶ Y),
      F.map ((Paths.of V).map e) ≫ a Y = a X ≫ G.map ((Paths.of V).map e)) : F ⟶ G where
  app := a
  naturality {X Y} p := by
    induction p with
    | nil =>
      change F.map (𝟙 X) ≫ a X = a X ≫ G.map (𝟙 X)
      rw [F.map_id, G.map_id, Category.id_comp, Category.comp_id]
    | cons p e ih =>
      change F.map (p ≫ (Paths.of V).map e) ≫ a _ =
        a X ≫ G.map (p ≫ (Paths.of V).map e)
      rw [F.map_comp, G.map_comp, Category.assoc]
      calc
        _ = F.map p ≫ (a _ ≫ G.map ((Paths.of V).map e)) :=
          congrArg (fun k => F.map p ≫ k) (ha e)
        _ = (F.map p ≫ a _) ≫ G.map ((Paths.of V).map e) := (Category.assoc _ _ _).symm
        _ = (a X ≫ G.map p) ≫ G.map ((Paths.of V).map e) :=
          congrArg (fun k => k ≫ G.map ((Paths.of V).map e)) ih
        _ = _ := Category.assoc _ _ _

end SerrePositivity.QuiverPaths
