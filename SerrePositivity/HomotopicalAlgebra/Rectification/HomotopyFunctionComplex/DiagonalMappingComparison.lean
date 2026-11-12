module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalMappingRows

/-!
# 中断した任意モデル源への一般化：DiagonalMappingComparison

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Identifying diagonal row comparisons with actual Hom precomposition。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0081][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0081
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Identifying diagonal row comparisons with actual Hom precomposition

The diagonal of the bisimplicial mapping object is naturally isomorphic to
the Hom of the diagonal cosimplicial object. The isomorphism is the identity
on simplices; its naturality uses the double diagram's commuting squares.
This identifies the concrete comparison map without assuming its weak
equivalence or any diagonal cofibrancy.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.DiagonalMappingComparison
variable {C : Type u} [Category.{v} C]

/-- Both sides have n-simplices A[n][n] to Z. -/
def iso (A : SimplexCategory ⥤ SimplexCategory ⥤ C) (Z : C) :
    DiagonalFrame.obj (DiagonalMappingRows.obj A Z) ≅
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (DiagonalFrame.obj A)).obj Z :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m f
    ext h
    change (A.obj m.unop).map f.unop ≫ ((A.map f.unop).app n.unop ≫ h) =
      ((A.map f.unop).app m.unop ≫ (A.obj n.unop).map f.unop) ≫ h
    rw [← CategoryTheory.Category.assoc, (A.map f.unop).naturality])

/-- Diagonalize the actual augmented row map. -/
def comparison {A : SimplexCategory ⥤ SimplexCategory ⥤ C} {B : SimplexCategory ⥤ C}
    (a : A ⟶ (Functor.const SimplexCategory).obj B) (Z : C) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).obj Z ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (DiagonalFrame.obj A)).obj Z :=
  (DiagonalFrame.constantIso ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).obj Z)).inv ≫
    DiagonalFrame.map (DiagonalMappingRows.comparison a Z) ≫ (iso A Z).hom

@[simp]
lemma comparison_eq {A : SimplexCategory ⥤ SimplexCategory ⥤ C} {B : SimplexCategory ⥤ C}
    (a : A ⟶ (Functor.const SimplexCategory).obj B) (Z : C) :
    comparison a Z = (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (DiagonalFrame.augmentation a)).app Z := by
  ext n h
  rfl

end SerrePositivity.HomotopyFunctionComplex.DiagonalMappingComparison
