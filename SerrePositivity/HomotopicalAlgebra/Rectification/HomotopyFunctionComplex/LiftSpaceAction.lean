module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.LiftSpace
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalHomComposition

/-!
# 中断した任意モデル源への一般化：LiftSpaceAction

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual actions of lift-space simplices on resolution Hom。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0105][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0105
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual actions of lift-space simplices on resolution Hom

A family of derived lifts and a family of target maps compose into the
Hom of the diagonal double diagram. At every strict lift point this is
exactly precomposition by the diagonal augmentation followed by that lift.
No diagonal cofibrancy, weak equivalence, or strict composition is assumed.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.HomotopyFunctionComplex.LiftSpaceAction
variable {C : Type u} [Category.{v} C]
  (A : SimplexCategory ⥤ SimplexCategory ⥤ C) {F B K : SimplexCategory ⥤ C}
  (a : A ⟶ (Functor.const SimplexCategory).obj F) (p : B ⟶ K) (f : F ⟶ K) (Z : C)

/-- All lift parameters act on actual simplices, naturally in the parameter. -/
abbrev parameterized {T : SSet.{v}} (s : T ⟶ LiftSpace.obj A a p f)
    (t : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).obj Z) :
    T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (DiagonalFrame.obj A)).obj Z :=
  DiagonalHom.pairing A B Z (s ≫ LiftSpace.inclusion A a p f) t

@[simp]
lemma parameterized_app {T : SSet.{v}} (s : T ⟶ LiftSpace.obj A a p f)
    (t : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).obj Z) (n : SimplexCategoryᵒᵖ) (x : T.obj n) :
    (parameterized A a p f Z s t).app n x =
      ((LiftSpace.inclusion A a p f).app n (s.app n x)).app n.unop ≫ t.app n x :=
  DiagonalHom.pairing_app A B Z _ _ n x

@[reassoc]
lemma parameterized_naturality {T U : SSet.{v}} (u : U ⟶ T)
    (s : T ⟶ LiftSpace.obj A a p f) (t : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).obj Z) :
    u ≫ parameterized A a p f Z s t = parameterized A a p f Z (u ≫ s) (u ≫ t) := by
  exact (DiagonalHom.pairing_naturality A B Z u _ _).trans
    (congrArg (fun k => DiagonalHom.pairing A B Z k (u ≫ t)) (Category.assoc _ _ _).symm)

/-- The universal action; its restriction along a parameter recovers the above map. -/
abbrev action : LiftSpace.obj A a p f ⨯ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).obj Z ⟶
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (DiagonalFrame.obj A)).obj Z :=
  parameterized A a p f Z prod.fst prod.snd

/-- A strict lift point acts by actual precomposition, after diagonal augmentation. -/
lemma ofLift {T : SSet.{v}}
    (d : T ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (e : F ⟶ B) (he : e ≫ p = f) (t : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).obj Z) :
    parameterized A a p f Z (d ≫ LiftSpace.ofLift A a p f e he) t =
      t ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (DiagonalFrame.augmentation a ≫ e)).app Z := by
  change DiagonalHom.pairing A B Z
    ((d ≫ LiftSpace.ofLift A a p f e he) ≫ LiftSpace.inclusion A a p f) t = _
  rw [Category.assoc, LiftSpace.ofLift_inclusion]
  ext n x
  exact DiagonalHom.pairing_app A B Z (d ≫ LiftSpace.point A a e) t n x

end SerrePositivity.HomotopyFunctionComplex.LiftSpaceAction
