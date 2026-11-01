module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexResolution

/-!
# 中断した任意モデル源への一般化：DiagonalFrame

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類C）。
対象：Diagonals of double cosimplicial objects。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0079][inventory]を参照する。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0079
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Diagonals of double cosimplicial objects

The construction and augmentation maps are ordinary category theory. Weak
augmentation statements use only the actual iterated Reedy resolution;
no diagonal cofibrancy or invariance theorem is assumed here.
-/

@[expose] public section
universe v u vI uI
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex.DiagonalFrame
variable {C : Type u} [Category.{v} C] {I : Type uI} [Category.{vI} I]

abbrev obj (A : I ⥤ I ⥤ C) : I ⥤ C := Functor.diag I ⋙ Functor.uncurry.obj A

@[simp]
lemma obj_obj (A : I ⥤ I ⥤ C) (i : I) : (obj A).obj i = (A.obj i).obj i := rfl

@[simp]
lemma obj_map (A : I ⥤ I ⥤ C) {i j : I} (f : i ⟶ j) :
    (obj A).map f = (A.map f).app i ≫ (A.obj j).map f := rfl

/-- Restrict a natural transformation of double diagrams to the diagonal. -/
def map {A A' : I ⥤ I ⥤ C} (a : A ⟶ A') : obj A ⟶ obj A' :=
  Functor.whiskerLeft (Functor.diag I) (Functor.uncurry.map a)

/-- The diagonal of an outer constant diagram is naturally its value. -/
def constantIso (B : I ⥤ C) : obj ((Functor.const I).obj B) ≅ B :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro i j f
    change (𝟙 _ ≫ B.map f) ≫ 𝟙 _ = 𝟙 _ ≫ B.map f
    simp only [Category.id_comp, Category.comp_id])

/-- An outer augmentation induces an actual augmentation of the diagonal. -/
def augmentation {A : I ⥤ I ⥤ C} {B : I ⥤ C}
    (a : A ⟶ (Functor.const I).obj B) : obj A ⟶ B where
  app i := (a.app i).app i
  naturality {i j} f := by
    change ((A.map f).app i ≫ (A.obj j).map f) ≫ (a.app j).app j =
      (a.app i).app i ≫ B.map f
    have ho := congr_app (a.naturality f) i
    change (A.map f).app i ≫ (a.app j).app i = (a.app i).app i ≫ 𝟙 _ at ho
    calc
      _ = (A.map f).app i ≫ ((a.app j).app i ≫ B.map f) := by
        rw [Category.assoc, (a.app j).naturality]
        rfl
      _ = _ := by rw [← Category.assoc, ho, Category.comp_id]

end SerrePositivity.HomotopyFunctionComplex.DiagonalFrame
