module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedDiagonalHom

/-!
# 中断した任意モデル源への一般化：MixedDiagonalHomRecovery

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Recover the original one-sided diagonal pairings from the mixed action。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0119][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0119
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Recover the original one-sided diagonal pairings from the mixed action

Fixing either ordinary endpoint gives exactly the existing diagonal Hom
pairing on the same whole parameter family, before Kan replacement.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite

namespace SerrePositivity.HomotopyFunctionComplex.MixedDiagonalHomRecovery
variable {C : Type u} [Category.{v} C]

def constantTargetIso (A : SimplexCategory ⥤ C) (Z : C) :
    MixedDiagonalHom.obj A ((Functor.const SimplexCategory).obj (op Z)) ≅
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Z :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m θ
    ext h
    change A.map θ.unop ≫ h ≫ (𝟙 (op Z)).unop = A.map θ.unop ≫ h
    exact congrArg (fun k => A.map θ.unop ≫ k) (Category.comp_id h))

def constantSourceEquiv (Z : C) (B : SimplexCategory ⥤ Cᵒᵖ) (n : SimplexCategoryᵒᵖ) :
    (MixedDiagonalHom.obj ((Functor.const SimplexCategory).obj Z) B).obj n ≃
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).obj (op Z)).obj n where
  toFun f := f.op
  invFun f := f.unop
  left_inv _ := rfl
  right_inv _ := rfl

def constantSourceIso (Z : C) (B : SimplexCategory ⥤ Cᵒᵖ) :
    MixedDiagonalHom.obj ((Functor.const SimplexCategory).obj Z) B ≅
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).obj (op Z) :=
  NatIso.ofComponents (fun n => (constantSourceEquiv Z B n).toIso) (by
    intro n m θ
    ext h
    apply (Quiver.Hom.unop_inj (C := C))
    change 𝟙 Z ≫ h ≫ (B.map θ.unop).unop = h ≫ (B.map θ.unop).unop
    exact Category.id_comp _)

lemma source_pairing {T : SSet.{v}} (D : SimplexCategory ⥤ SimplexCategory ⥤ C)
    (A : SimplexCategory ⥤ C) (Z : C) (s : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom D).obj A)
    (t : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Z) :
    MixedDiagonalHom.pre (CosimplicialMapFamily.ofDoubleHom s)
        (t ≫ (constantTargetIso A Z).inv) ≫ (constantTargetIso (DiagonalFrame.obj D) Z).hom =
      DiagonalHom.pairing D A Z s t := by
  ext n x
  change (𝟙 ((DiagonalFrame.obj D).obj n.unop ⟶ Z))
      ((MixedDiagonalHom.pre (CosimplicialMapFamily.ofDoubleHom s)
    (t ≫ (constantTargetIso A Z).inv)).app n x) = (DiagonalHom.pairing D A Z s t).app n x
  rw [types_id_apply, MixedDiagonalHom.pre_app, DiagonalHom.pairing_app]
  change (s.app n x).app n.unop ≫ (𝟙 (A.obj n.unop ⟶ Z)) (t.app n x) = _
  rw [types_id_apply]

lemma target_pairing {T : SSet.{v}} (E : SimplexCategory ⥤ SimplexCategory ⥤ Cᵒᵖ)
    (B : SimplexCategory ⥤ Cᵒᵖ) (Z : C) (r : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom E).obj B)
    (t : T ⟶ MixedDiagonalHom.obj ((Functor.const SimplexCategory).obj Z) B) :
    MixedDiagonalHom.post (CosimplicialMapFamily.ofDoubleHom r) t ≫
        (constantSourceIso Z (DiagonalFrame.obj E)).hom =
      DiagonalHom.pairing E B (op Z) r (t ≫ (constantSourceIso Z B).hom) := by
  ext n x
  change ((MixedDiagonalHom.post (CosimplicialMapFamily.ofDoubleHom r) t).app n x).op =
    (DiagonalHom.pairing E B (op Z) r (t ≫ (constantSourceIso Z B).hom)).app n x
  rw [DiagonalHom.pairing_app]
  apply (Quiver.Hom.unop_inj (C := C))
  exact MixedDiagonalHom.post_app (C := C) (CosimplicialMapFamily.ofDoubleHom r) t n x

end SerrePositivity.HomotopyFunctionComplex.MixedDiagonalHomRecovery
