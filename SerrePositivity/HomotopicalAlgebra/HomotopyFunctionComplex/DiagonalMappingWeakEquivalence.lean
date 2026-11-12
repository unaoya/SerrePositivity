module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalQuillen
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.DiagonalMappingComparison
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionLiftAction

/-!
# 中断した任意モデル源への一般化：DiagonalMappingWeakEquivalence

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類C）。
対象：The actual diagonal resolution Hom comparison is a weak equivalence。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0083][inventory]を参照する。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0083
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual diagonal resolution Hom comparison is a weak equivalence

The proved bisimplicial diagonal theorem applies to the actual rowwise
comparison. This needs neither diagonal cofibrancy of a double source
resolution nor functorial factorizations on the arbitrary model source.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex.DiagonalMappingComparison
variable {C : Type u} [Category.{v} C]
  [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma weakEquivalence {A : SimplexCategory ⥤ SimplexCategory ⥤ C} {B : SimplexCategory ⥤ C}
    (a : A ⟶ (Functor.const SimplexCategory).obj B) (Z : C)
    (ha : ∀ n, weakEquivalences SSet.{v} ((DiagonalMappingRows.comparison a Z).app n)) :
    weakEquivalences SSet.{v} ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (DiagonalFrame.augmentation a)).app Z) := by
  have hD := BisimplicialModel.diagonal_map_weakEquivalence hcof hfib
    (DiagonalMappingRows.comparison a Z) ha
  have h := (weakEquivalences SSet.{v}).comp_mem _ _
    ((weakEquivalences SSet.{v}).of_isIso
      (DiagonalFrame.constantIso ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).obj Z)).inv)
    ((weakEquivalences SSet.{v}).comp_mem _ _ hD
      ((weakEquivalences SSet.{v}).of_isIso (iso A Z).hom))
  change weakEquivalences SSet.{v} (comparison a Z) at h
  exact comparison_eq a Z ▸ h

variable [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := simplexModelCategory C

include hcof hfib in
lemma resolution_weakEquivalence {B : SimplexCategory ⥤ C}
    (q : CofibrantResolution simplex B)
    (hB : reedyLeft simplex (cofibrations C) (initial.to B)) (Z : C) [IsFibrant Z] :
    weakEquivalences SSet.{v}
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (DiagonalFrame.augmentation q.augmentation)).app Z) :=
  weakEquivalence hcof hfib q.augmentation Z
    (DiagonalMappingRows.comparison_weakEquivalence q hcof hB Z)

include hcof hfib in
/-- This is the comparison used by the actual higher-lift action on every model source. -/
lemma liftAction_comparison_weakEquivalence (X : ResolutionObject C) (Z : C) [IsFibrant Z] :
    weakEquivalences SSet.{v} (ResolutionLiftAction.comparison X Z) :=
  resolution_weakEquivalence hcof hfib (ResolutionLiftSpace.frame X) X.resolution.cofibrant Z

end SerrePositivity.HomotopyFunctionComplex.DiagonalMappingComparison
