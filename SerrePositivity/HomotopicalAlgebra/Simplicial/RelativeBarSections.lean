module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarConstruction
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.UniverseLiftFillers

/-!
# 相対barへのsectionの区間が全単体作用素と整合する

## 概要
相対barへのsectionの区間が全単体作用素と整合する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
各次数の要素の圏・comma圏とnerveを使って写像を構成する。
単体方向と基底方向の自然性を確認し、収縮や局所化の普遍性へ接続する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。
[棚卸し m0530][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0530
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual sections into a relative bar and their comma-arrow intervals

All source, value, and base universes are independent. The interval uses
one actual comma morphism, retaining its element labels in every degree.
-/

@[expose] public section
universe v uD vD uB vB
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable {D : Type uD} [Category.{vD} D] {B : Type uB} [Category.{vB} B]
  (p : D ⥤ B) (F : D ⥤ SSet.{v}) {b : B} {d e : D}

abbrev sectionPoint (α : p.obj d ⟶ b) (n : SimplexCategoryᵒᵖ) (x : (F.obj d).obj n) :
    CostructuredArrow (elementProjection p F n) b :=
  CostructuredArrow.mk (Y := (F.flip.obj n).elementsMk d x) α

def commaSection (α : p.obj d ⟶ b) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max uD vD vB} (F.obj d) ⟶ (relative p F).obj b where
  app n := ↾fun x => (Functor.const (Fin (n.unop.len + 1))).obj (sectionPoint p F α n x.down)
  naturality {_ _} _ := rfl

variable (α : p.obj d ⟶ b) (β : p.obj e ⟶ b) (k : d ⟶ e) (hk : p.map k ≫ β = α)

abbrev sectionArrow (n : SimplexCategoryᵒᵖ) (x : (F.obj d).obj n) :
    sectionPoint p F α n x ⟶ sectionPoint p F β n ((F.map k).app n x) :=
  CostructuredArrow.homMk (Functor.Elements.homMk k rfl) hk

abbrev sectionInterval (n : SimplexCategoryᵒᵖ) (x : (F.obj d).obj n) :=
  ComposableArrows.mk₁ (sectionArrow p F α β k hk n x)

abbrev sectionLevelMap {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :=
  ((commaLevels p F).map θ).app b |>.toFunctor

lemma sectionInterval_operator_obj {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (x : (F.obj d).obj n) (q : Fin 2) :
    (sectionInterval p F α β k hk n x ⋙ sectionLevelMap p F θ).obj q =
      (sectionInterval p F α β k hk m ((F.obj d).map θ x)).obj q := by
  fin_cases q
  · rfl
  · exact congrArg (sectionPoint p F β m)
      (congrArg (fun f => f x) ((F.map k).naturality θ)).symm

lemma elementComma_hom_heq {n : SimplexCategoryᵒᵖ}
    {a a' c c' : CostructuredArrow (elementProjection p F n) b}
    (ha : a = c) (ha' : a' = c') (f : a ⟶ a') (g : c ⟶ c')
    (h : f.left.hom ≍ g.left.hom) : f ≍ g := by
  cases ha
  cases ha'
  apply heq_of_eq
  apply CostructuredArrow.hom_ext
  apply Functor.Elements.hom_ext
  exact eq_of_heq h

/- 旧宣言の技術注記：
The entire interval commutes with all operators, including its mixed 0→1 arrow.
-/
/-- 相対barへのsectionの区間が全単体作用素と整合する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
各次数の要素の圏・comma圏とnerveを使って写像を構成する。
単体方向と基底方向の自然性を確認し、収縮や局所化の普遍性へ接続する。
-/
lemma sectionInterval_operator {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (x : (F.obj d).obj n) :
    sectionInterval p F α β k hk n x ⋙ sectionLevelMap p F θ =
      sectionInterval p F α β k hk m ((F.obj d).map θ x) := by
  apply CategoryTheory.Functor.hext (sectionInterval_operator_obj p F α β k hk θ x)
  intro i j f
  apply elementComma_hom_heq p F
    (sectionInterval_operator_obj p F α β k hk θ x i)
    (sectionInterval_operator_obj p F α β k hk θ x j)
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · have h := leOfHom f
    change (1 : Fin 2) ≤ 0 at h
    exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) h)
  · rfl

end SerrePositivity.SimplicialModel.BarConstruction
