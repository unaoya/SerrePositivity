module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalDiagram
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionHom
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite

/-!
# 中断した任意モデル源への一般化：DiagonalHomComposition

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類C）。
対象：Actual composition from double resolutions into diagonal Hom。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0080][inventory]を参照する。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0080
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual composition from double resolutions into diagonal Hom

An n-simplex of Hom(A,B) is an actual natural transformation A[n] to B.
Its n-th component composes with an n-simplex of Hom(B,Z). This is a
simplicial map to Hom(diag A,Z), before imposing any model conditions.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.HomotopyFunctionComplex.DiagonalHom
variable {C : Type u} [Category.{v} C]
  (A : SimplexCategory ⥤ SimplexCategory ⥤ C) (B : SimplexCategory ⥤ C) (Z : C)

abbrev source : SSet.{v} :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj B ⨯ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).obj Z

abbrev first : source A B Z ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj B := prod.fst
abbrev second : source A B Z ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).obj Z := prod.snd

/-- Actual degreewise composition, with simplicial naturality. -/
def composition : source A B Z ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (DiagonalFrame.obj A)).obj Z where
  app n := ↾fun x =>
    (((first A B Z).app n) x).app n.unop ≫
      ((second A B Z).app n) x
  naturality {n m} g := by
    ext x
    have h₁ := congrArg (fun k => k x)
      ((first A B Z).naturality g)
    have h₂ := congrArg (fun k => k x)
      ((second A B Z).naturality g)
    let s := ((first A B Z).app n) x
    let t := ((second A B Z).app n) x
    change (((first A B Z).app m) ((source A B Z).map g x)) = A.map g.unop ≫ s at h₁
    change (((second A B Z).app m) ((source A B Z).map g x)) = B.map g.unop ≫ t at h₂
    change ((((first A B Z).app m) ((source A B Z).map g x)).app m.unop) ≫
        (((second A B Z).app m) ((source A B Z).map g x)) =
      ((A.map g.unop).app m.unop ≫ (A.obj n.unop).map g.unop) ≫ (s.app n.unop ≫ t)
    rw [h₁, h₂]
    change ((A.map g.unop).app m.unop ≫ s.app m.unop) ≫ (B.map g.unop ≫ t) = _
    rw [Category.assoc, ← Category.assoc (s.app m.unop), ← s.naturality g.unop]
    simp only [Category.assoc]
    rfl

@[simp]
lemma composition_app (n : SimplexCategoryᵒᵖ) (x : (source A B Z).obj n) :
    (composition A B Z).app n x =
      (((first A B Z).app n) x).app n.unop ≫
        ((second A B Z).app n) x := rfl

/-- Composition with both simplices parameterized by the same simplicial set. -/
abbrev pairing {T : SSet.{v}} (a : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj B)
    (b : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).obj Z) :
    T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (DiagonalFrame.obj A)).obj Z :=
  prod.lift a b ≫ composition A B Z

@[simp]
lemma pairing_app {T : SSet.{v}} (a : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj B)
    (b : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).obj Z) (n : SimplexCategoryᵒᵖ) (x : T.obj n) :
    (pairing A B Z a b).app n x = (a.app n x).app n.unop ≫ b.app n x := by
  change (((first A B Z).app n) ((prod.lift a b).app n x)).app n.unop ≫
    ((second A B Z).app n) ((prod.lift a b).app n x) = _
  have h₁ := congrArg (fun k => k.app n x) (prod.lift_fst a b)
  have h₂ := congrArg (fun k => k.app n x) (prod.lift_snd a b)
  change ((first A B Z).app n) ((prod.lift a b).app n x) = a.app n x at h₁
  change ((second A B Z).app n) ((prod.lift a b).app n x) = b.app n x at h₂
  rw [h₁, h₂]

@[reassoc]
lemma pairing_naturality {T U : SSet.{v}} (u : U ⟶ T)
    (a : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj B) (b : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).obj Z) :
    u ≫ pairing A B Z a b = pairing A B Z (u ≫ a) (u ≫ b) := by
  ext n x
  change (pairing A B Z a b).app n (u.app n x) = _
  exact (pairing_app A B Z a b n (u.app n x)).trans
    (pairing_app A B Z (u ≫ a) (u ≫ b) n x).symm

/-- Postcomposition in the ordinary target commutes with the actual pairing. -/
lemma pairing_target_naturality {Z' : C} (h : Z ⟶ Z') {T : SSet.{v}}
    (a : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj B) (b : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).obj Z) :
    pairing A B Z' a (b ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).map h) =
      pairing A B Z a b ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (DiagonalFrame.obj A)).map h := by
  ext n x
  exact (pairing_app A B Z' a (b ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).map h) n x).trans
    ((Category.assoc ((a.app n x).app n.unop) (b.app n x) h).symm.trans
      (congrArg (fun k => k ≫ h) (pairing_app A B Z a b n x).symm))

/-- Composition through an actual map of the intermediate resolution is associative. -/
lemma pairing_middle_naturality {B' : SimplexCategory ⥤ C} (k : B ⟶ B') {T : SSet.{v}}
    (a : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj B) (b : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B').obj Z) :
    pairing A B' Z (a ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map k) b =
      pairing A B Z a (b ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap k).app Z) := by
  ext n x
  exact (pairing_app A B' Z (a ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map k) b n x).trans
    ((Category.assoc ((a.app n x).app n.unop) (k.app n.unop) (b.app n x)).trans
      (pairing_app A B Z a (b ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap k).app Z) n x).symm)

/-- Source change is compatible with restriction of a double diagram to the diagonal. -/
lemma pairing_source_naturality {A' : SimplexCategory ⥤ SimplexCategory ⥤ C}
    (φ : A ⟶ A') {T : SSet.{v}} (a : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A').obj B)
    (b : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).obj Z) :
    pairing A B Z (a ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap φ).app B) b =
      pairing A' B Z a b ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (DiagonalFrame.map φ)).app Z := by
  ext n x
  exact (pairing_app A B Z (a ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap φ).app B) b n x).trans
    ((Category.assoc ((φ.app n.unop).app n.unop) ((a.app n x).app n.unop) (b.app n x)).trans
      (congrArg (fun k => (φ.app n.unop).app n.unop ≫ k)
        (pairing_app A' B Z a b n x)).symm)

end SerrePositivity.HomotopyFunctionComplex.DiagonalHom
