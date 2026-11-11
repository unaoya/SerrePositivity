module
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexResolution

public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalDiagram

/-!
分割で生成：docstring を書き直すこと
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

namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison
variable {C : Type u} [Category.{v} C] {I : Type uI} [Category.{vI} I]

variable [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C

abbrev resolution (B : SimplexCategory ⥤ C) := Reedy.cosimplicialResolution B

abbrev resolutionObj (B : SimplexCategory ⥤ C) : SimplexCategory ⥤ C :=
  _root_.SerrePositivity.HomotopyFunctionComplex.DiagonalFrame.obj (resolution B).obj

abbrev resolutionAugmentation (B : SimplexCategory ⥤ C) : resolutionObj B ⟶ B :=
  _root_.SerrePositivity.HomotopyFunctionComplex.DiagonalFrame.augmentation (resolution B).augmentation

lemma resolutionAugmentation_weakEquivalence (B : SimplexCategory ⥤ C)
    (n : SimplexCategory) : weakEquivalences C ((resolutionAugmentation B).app n) :=
  (resolution B).augmentation_weakEquivalence n n

lemma resolutionObj_homotopicallyConstant (B : SimplexCategory ⥤ C)
    (hB : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))
    {n m : SimplexCategory} (f : n ⟶ m) :
    weakEquivalences C ((resolutionObj B).map f) := by
  have h := (resolutionAugmentation B).naturality f
  exact (weakEquivalences C).of_postcomp _ _
    (resolutionAugmentation_weakEquivalence B m)
    (h.symm ▸ (weakEquivalences C).comp_mem _ _
      (resolutionAugmentation_weakEquivalence B n) (hB f))

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison
