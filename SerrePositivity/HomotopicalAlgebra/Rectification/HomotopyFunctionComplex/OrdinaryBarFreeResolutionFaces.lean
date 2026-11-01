module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.FreePathResolution
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeDiagramExtension

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFreeResolutionFaces

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The first two free-resolution faces of the actual choice-cover functor。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0184][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0184
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The first two free-resolution faces of the actual choice-cover functor

Both faces have the same entire base projection. The degeneracy splits
both of them as strict functor equalities. Their lifted values are not
asserted equal before supplying a relative comparison.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionFaces
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

def faceZero (P : SSet.{max u v}) : Paths (Paths (Cᵒᵖ × C)) ⥤
    OrdinaryBarFreeDiagramExtension.target (C := C) hcof hfib P :=
  FreePathResolution.counit (Paths (Cᵒᵖ × C)) ⋙
    OrdinaryBarFreeDiagramExtension.freeCover hcof hfib P

def faceOne (P : SSet.{max u v}) : Paths (Paths (Cᵒᵖ × C)) ⥤
    OrdinaryBarFreeDiagramExtension.target (C := C) hcof hfib P :=
  FreePathResolution.map (FreePathResolution.counit (Cᵒᵖ × C)) ⋙
    OrdinaryBarFreeDiagramExtension.freeCover hcof hfib P

lemma projection_equal (P : SSet.{max u v}) :
    faceZero (C := C) hcof hfib P ⋙ OrdinaryBarChoiceCategory.projection hcof hfib P =
      faceOne hcof hfib P ⋙ OrdinaryBarChoiceCategory.projection hcof hfib P := by
  simp only [faceZero, faceOne, CategoryTheory.Functor.assoc,
    OrdinaryBarFreeDiagramExtension.freeCover_projection, FreePathResolution.lift_identity]
  exact (FreePathResolution.counit_naturality (FreePathResolution.counit (Cᵒᵖ × C))).symm

lemma degeneracy_faceZero (P : SSet.{max u v}) :
    FreePathResolution.duplicate (Cᵒᵖ × C) ⋙ faceZero hcof hfib P =
      OrdinaryBarFreeDiagramExtension.freeCover hcof hfib P := by
  change (FreePathResolution.duplicate (Cᵒᵖ × C) ⋙
    FreePathResolution.counit (Paths (Cᵒᵖ × C))) ⋙
      OrdinaryBarFreeDiagramExtension.freeCover hcof hfib P = _
  rw [FreePathResolution.left_counit, CategoryTheory.Functor.id_comp]

lemma degeneracy_faceOne (P : SSet.{max u v}) :
    FreePathResolution.duplicate (Cᵒᵖ × C) ⋙ faceOne hcof hfib P =
      OrdinaryBarFreeDiagramExtension.freeCover hcof hfib P := by
  change (FreePathResolution.duplicate (Cᵒᵖ × C) ⋙
    FreePathResolution.map (FreePathResolution.counit (Cᵒᵖ × C))) ⋙
      OrdinaryBarFreeDiagramExtension.freeCover hcof hfib P = _
  rw [FreePathResolution.right_counit, CategoryTheory.Functor.id_comp]

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionFaces
