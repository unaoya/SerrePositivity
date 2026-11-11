module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalDiagram
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SourceInvariance

/-!
# 中断した任意モデル源への一般化：DiagonalMappingRows

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類C）。
対象：Rowwise comparisons for a double resolution mapping object。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0082][inventory]を参照する。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0082
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Rowwise comparisons for a double resolution mapping object

The augmented bisimplicial mapping object has actual weak equivalences in
every row. This is not yet a diagonal weak equivalence theorem.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex.DiagonalMappingRows
variable {C : Type u} [Category.{v} C]

abbrev obj (A : SimplexCategory ⥤ SimplexCategory ⥤ C) (Z : C) :
    SimplexCategoryᵒᵖ ⥤ SSet.{v} := A.op ⋙ cosimplicialHomSource Z

/-- The constant original mapping space maps naturally to all outer rows. -/
def comparison {A : SimplexCategory ⥤ SimplexCategory ⥤ C} {B : SimplexCategory ⥤ C}
    (a : A ⟶ (Functor.const SimplexCategory).obj B) (Z : C) :
    (Functor.const SimplexCategoryᵒᵖ).obj ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).obj Z) ⟶ obj A Z where
  app n := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (a.app n.unop)).app Z
  naturality {n m} f := by
    ext k h
    change (a.app m.unop).app k.unop ≫ h =
      (A.map f.unop).app k.unop ≫ ((a.app n.unop).app k.unop ≫ h)
    have he := congr_app (a.naturality f.unop) k.unop
    change (A.map f.unop).app k.unop ≫ (a.app n.unop).app k.unop =
      (a.app m.unop).app k.unop ≫ 𝟙 _ at he
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun t => t ≫ h) (he.trans (Category.comp_id _)))).symm

variable [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := simplexModelCategory C
variable {B : SimplexCategory ⥤ C} (q : CofibrantResolution simplex B)

lemma row_cofibrant (n : SimplexCategory) :
    reedyLeft simplex (cofibrations C) (initial.to (q.obj.obj n)) := by
  exact (q.isCofibrant_obj n).mem

lemma row_homotopicallyConstant
    (hB : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))
    (k : SimplexCategory) {n m : SimplexCategory} (f : n ⟶ m) :
    weakEquivalences C ((q.obj.obj k).map f) := by
  have he := (q.augmentation.app k).naturality f
  exact (weakEquivalences C).of_postcomp _ _
    (q.augmentation_weakEquivalence k m)
    (he.symm ▸ (weakEquivalences C).comp_mem _ _
      (q.augmentation_weakEquivalence k n) (hB f))

lemma row_kanComplex
    (hB : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))
    (n : SimplexCategoryᵒᵖ) (Z : C) [IsFibrant Z] :
    SSet.KanComplex ((obj q.obj Z).obj n) :=
  cosimplicialHom_kanComplex _ (row_cofibrant q n.unop)
    (row_homotopicallyConstant q hB n.unop) Z

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma comparison_weakEquivalence
    (hB : reedyLeft simplex (cofibrations C) (initial.to B))
    (Z : C) [IsFibrant Z] (n : SimplexCategoryᵒᵖ) :
    weakEquivalences SSet.{v} ((comparison q.augmentation Z).app n) :=
  cosimplicialHomMap_weakEquivalence hcof (q.augmentation.app n.unop)
    (row_cofibrant q n.unop) hB (q.augmentation_weakEquivalence n.unop) Z

end SerrePositivity.HomotopyFunctionComplex.DiagonalMappingRows
