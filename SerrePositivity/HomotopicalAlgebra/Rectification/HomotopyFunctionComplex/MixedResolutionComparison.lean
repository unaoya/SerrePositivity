module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedDiagonalRows
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedBiresolutionComparison

/-!
# 中断した任意モデル源への一般化：MixedResolutionComparison

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual two-sided frame augmentation is a natural weak equivalence。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0125][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0125
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual two-sided frame augmentation is a natural weak equivalence

Change the target first, then the source. Pointwise cofibrancy of the
original resolution and of the double frame rows suffices; diagonal
Reedy cofibrancy is not required.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite

namespace SerrePositivity.HomotopyFunctionComplex.MixedResolutionComparison
variable {C : Type u} [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C
local instance : ModelCategory (SimplexCategory ⥤ Cᵒᵖ) := Reedy.simplexModelCategory Cᵒᵖ

abbrev augmentation (X : ResolutionObject C) :=
  DiagonalFrame.augmentation (ResolutionLiftSpace.frame X).augmentation

lemma target_isFibrant (Y : ResolutionObject Cᵒᵖ) (n : SimplexCategory) :
    IsFibrant (((DiagonalFrame.obj (ResolutionLiftSpace.frame Y).obj).obj n).unop) := by
  have : IsCofibrant (((ResolutionLiftSpace.frame Y).obj.obj n).obj n) :=
    cosimplicialFrame_isCofibrant_obj _
      (DiagonalMappingRows.row_cofibrant (ResolutionLiftSpace.frame Y) n) n
  exact (isFibrant_iff_of_isTerminal
    (initial.to (((ResolutionLiftSpace.frame Y).obj.obj n).obj n)).unop
    (terminalUnopOfInitial initialIsInitial)).mpr inferInstance

def output : RightResolutionMapping.Index C ⥤ SSet.{v} where
  obj X := MixedResolutionLiftAction.output X.1.unop.inner X.2.unop.inner
  map f := MixedDiagonalHom.map (FramedResolution.diagonal.map f.1.unop)
    (FramedResolution.diagonal.map f.2.unop)
  map_id X := by
    change MixedDiagonalHom.map (FramedResolution.diagonal.map (𝟙 X.1.unop))
      (FramedResolution.diagonal.map (𝟙 X.2.unop)) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    exact MixedDiagonalHom.map_id _ _
  map_comp f g := by
    change MixedDiagonalHom.map (FramedResolution.diagonal.map (g.1.unop ≫ f.1.unop))
      (FramedResolution.diagonal.map (g.2.unop ≫ f.2.unop)) = _
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    exact MixedDiagonalHom.map_comp _ _ _ _

def comparison : MixedBiresolutionComparison.functor (C := C) ⟶ output where
  app X := MixedDiagonalHom.map (augmentation X.1.unop.inner) (augmentation X.2.unop.inner)
  naturality {X Y} f := by
    change MixedDiagonalHom.map f.1.unop.map.diagram f.2.unop.map.diagram ≫
        MixedDiagonalHom.map (augmentation Y.1.unop.inner) (augmentation Y.2.unop.inner) =
      MixedDiagonalHom.map (augmentation X.1.unop.inner) (augmentation X.2.unop.inner) ≫
        MixedDiagonalHom.map (FramedResolution.diagonal.map f.1.unop)
          (FramedResolution.diagonal.map f.2.unop)
    rw [← MixedDiagonalHom.map_comp, ← MixedDiagonalHom.map_comp]
    exact congrArg₂ MixedDiagonalHom.map
      (FramedResolution.augmentation.naturality f.1.unop).symm
      (FramedResolution.augmentation.naturality f.2.unop).symm

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma target_weakEquivalence (X : ResolutionObject C) (Y : ResolutionObject Cᵒᵖ) :
    weakEquivalences SSet.{v}
      (MixedDiagonalHom.map (𝟙 X.resolution.obj) (augmentation Y)) := by
  apply MixedDiagonalRows.right_weakEquivalence hcof hfib
  intro n
  have : IsCofibrant (X.resolution.obj.obj n.unop) := X.resolution.isCofibrant_obj n.unop
  have : IsFibrant (op (X.resolution.obj.obj n.unop)) :=
    (isFibrant_iff_of_isTerminal (initial.to (X.resolution.obj.obj n.unop)).op
      (terminalOpOfInitial initialIsInitial)).mpr inferInstance
  exact DiagonalMappingComparison.liftAction_comparison_weakEquivalence hcof hfib Y _

include hcof hfib in
lemma source_weakEquivalence (X : ResolutionObject C) (Y : ResolutionObject Cᵒᵖ) :
    weakEquivalences SSet.{v} (MixedDiagonalHom.map (augmentation X)
      (𝟙 (DiagonalFrame.obj (ResolutionLiftSpace.frame Y).obj))) := by
  apply MixedDiagonalRows.left_weakEquivalence hcof hfib
  intro n
  have := target_isFibrant Y n.unop
  exact DiagonalMappingComparison.liftAction_comparison_weakEquivalence hcof hfib X _

include hcof hfib in
lemma augmentation_weakEquivalence (X : ResolutionObject C) (Y : ResolutionObject Cᵒᵖ) :
    weakEquivalences SSet.{v}
      (MixedDiagonalHom.map (augmentation X) (augmentation Y)) := by
  have h := (weakEquivalences SSet.{v}).comp_mem _ _
    (target_weakEquivalence hcof hfib X Y) (source_weakEquivalence hcof hfib X Y)
  rw [← MixedDiagonalHom.map_comp, Category.comp_id, Category.id_comp] at h
  exact h

include hcof hfib in
lemma comparison_weakEquivalence (X : RightResolutionMapping.Index C) :
    weakEquivalences SSet.{v} ((comparison (C := C)).app X) :=
  augmentation_weakEquivalence hcof hfib X.1.unop.inner X.2.unop.inner

end SerrePositivity.HomotopyFunctionComplex.MixedResolutionComparison
