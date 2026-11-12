module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.LiftSpace
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# 中断した任意モデル源への一般化：LiftSpaceFunctor

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Strict functoriality of lift spaces in augmented targets。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0106][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0106
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Strict functoriality of lift spaces in augmented targets

The actual pullback fiber, rather than a chosen contractible replacement,
varies functorially over a fixed base. Projection to the point is natural.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.HomotopyFunctionComplex.LiftSpace
variable {C : Type u} [Category.{v} C] (A : SimplexCategory ⥤ C) {X B : C}
  (a : A ⟶ (Functor.const SimplexCategory).obj X) (f : X ⟶ B)

/-- Postcompose a lift along an actual morphism over B. -/
def map {E E' : C} {p : E ⟶ B} {p' : E' ⟶ B} (k : E ⟶ E') (hk : k ≫ p' = p) :
    obj A a p f ⟶ obj A a p' f :=
  pullback.lift (inclusion A a p f ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map k) (projection A a p f) (by
    rw [Category.assoc, ← (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map_comp, hk]
    exact over A a p f)

@[reassoc (attr := simp)]
lemma map_inclusion {E E' : C} {p : E ⟶ B} {p' : E' ⟶ B}
    (k : E ⟶ E') (hk : k ≫ p' = p) :
    map A a f k hk ≫ inclusion A a p' f =
      inclusion A a p f ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map k := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma map_projection {E E' : C} {p : E ⟶ B} {p' : E' ⟶ B}
    (k : E ⟶ E') (hk : k ≫ p' = p) :
    map A a f k hk ≫ projection A a p' f = projection A a p f := pullback.lift_snd _ _ _

/-- Strict target functoriality, without choosing any factorizations. -/
def functor : Over B ⥤ SSet.{v} where
  obj E := obj A a E.hom f
  map k := map A a f k.left k.w
  map_id E := by
    apply pullback.hom_ext <;>
      simp only [map_inclusion, map_projection, Over.id_left,
        CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  map_comp {E E' E''} k l := by
    apply pullback.hom_ext <;>
      simp only [map_inclusion, map_projection, map_inclusion_assoc,
        Over.comp_left,
        CategoryTheory.Functor.map_comp, Category.assoc]
    rfl

/-- All the fibers project naturally to the same point. -/
def projectionNatTrans : functor A a f ⟶
    (Functor.const (Over B)).obj (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) where
  app E := projection A a E.hom f
  naturality {E E'} k := by
    change map A a f k.left k.w ≫ projection A a E'.hom f =
      projection A a E.hom f ≫ 𝟙 _
    rw [map_projection, Category.comp_id]

end SerrePositivity.HomotopyFunctionComplex.LiftSpace
