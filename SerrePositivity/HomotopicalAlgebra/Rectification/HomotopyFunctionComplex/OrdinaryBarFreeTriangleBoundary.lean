module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.FreePathResolutionDegreeTwo
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeResolutionComparison

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFreeTriangleBoundary

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual triangle edges and their vertex and degeneracy overlaps。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0191][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0191
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual triangle edges and their vertex and degeneracy overlaps

The three edges are pullbacks of the existing comparison, rather than new
independent choices. Their endpoint and degeneracy restrictions are strict
functor equalities. Gluing the parameter boundary and its relative filler
are separate subsequent constructions.
-/

@[expose] public section
universe v u w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeTriangleBoundary
open OrdinaryBarFreeDiagramExtension
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})

abbrev base := Cᵒᵖ × C
abbrev source := Paths (Paths (Paths (base (C := C))))
abbrev interval := SSet.stdSimplex.{w}.obj (SimplexCategory.mk 1)

abbrev vertex0 : source (C := C) ⥤ target (C := C) hcof hfib P :=
  FreePathResolutionDegreeTwo.faceZero (base (C := C)) ⋙
    OrdinaryBarFreeResolutionFaces.faceZero hcof hfib P
abbrev vertex1 : source (C := C) ⥤ target (C := C) hcof hfib P :=
  FreePathResolutionDegreeTwo.faceZero (base (C := C)) ⋙
    OrdinaryBarFreeResolutionFaces.faceOne hcof hfib P
abbrev vertex2 : source (C := C) ⥤ target (C := C) hcof hfib P :=
  FreePathResolutionDegreeTwo.faceOne (base (C := C)) ⋙
    OrdinaryBarFreeResolutionFaces.faceOne hcof hfib P

abbrev edge01 : source (C := C) ⥤ target (C := C) hcof hfib (P ⊗ interval) :=
  FreePathResolutionDegreeTwo.faceZero (base (C := C)) ⋙
    OrdinaryBarFreeResolutionComparison.comparison hcof hfib P
abbrev edge02 : source (C := C) ⥤ target (C := C) hcof hfib (P ⊗ interval) :=
  FreePathResolutionDegreeTwo.faceOne (base (C := C)) ⋙
    OrdinaryBarFreeResolutionComparison.comparison hcof hfib P
abbrev edge12 : source (C := C) ⥤ target (C := C) hcof hfib (P ⊗ interval) :=
  FreePathResolutionDegreeTwo.faceTwo (base (C := C)) ⋙
    OrdinaryBarFreeResolutionComparison.comparison hcof hfib P

lemma edge01_zero : edge01 (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₀ = vertex0 hcof hfib P := by
  rw [edge01, CategoryTheory.Functor.assoc, OrdinaryBarFreeResolutionComparison.comparison_zero]

lemma edge01_one : edge01 (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₁ = vertex1 hcof hfib P := by
  rw [edge01, CategoryTheory.Functor.assoc, OrdinaryBarFreeResolutionComparison.comparison_one]

lemma edge02_zero : edge02 (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₀ = vertex0 hcof hfib P := by
  rw [edge02, CategoryTheory.Functor.assoc, OrdinaryBarFreeResolutionComparison.comparison_zero]
  change (FreePathResolutionDegreeTwo.faceOne (base (C := C)) ⋙
    FreePathResolutionDegreeTwo.lowerZero (base (C := C))) ⋙ freeCover hcof hfib P = _
  rw [FreePathResolutionDegreeTwo.faceOne_lowerZero]
  rfl

lemma edge02_one : edge02 (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₁ = vertex2 hcof hfib P := by
  rw [edge02, CategoryTheory.Functor.assoc, OrdinaryBarFreeResolutionComparison.comparison_one]

lemma edge12_zero : edge12 (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₀ = vertex1 hcof hfib P := by
  rw [edge12, CategoryTheory.Functor.assoc, OrdinaryBarFreeResolutionComparison.comparison_zero]
  change (FreePathResolutionDegreeTwo.faceTwo (base (C := C)) ⋙
    FreePathResolutionDegreeTwo.lowerZero (base (C := C))) ⋙ freeCover hcof hfib P = _
  rw [FreePathResolutionDegreeTwo.faceTwo_lowerZero]
  rfl

lemma edge12_one : edge12 (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₁ = vertex2 hcof hfib P := by
  rw [edge12, CategoryTheory.Functor.assoc, OrdinaryBarFreeResolutionComparison.comparison_one]
  change (FreePathResolutionDegreeTwo.faceTwo (base (C := C)) ⋙
    FreePathResolutionDegreeTwo.lowerOne (base (C := C))) ⋙ freeCover hcof hfib P = _
  rw [FreePathResolutionDegreeTwo.faceTwo_lowerOne]
  rfl

lemma vertex0_overlap : edge01 (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₀ =
      edge02 hcof hfib P ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₀ :=
  (edge01_zero hcof hfib P).trans (edge02_zero hcof hfib P).symm

lemma vertex1_overlap : edge01 (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₁ =
      edge12 hcof hfib P ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₀ :=
  (edge01_one hcof hfib P).trans (edge12_zero hcof hfib P).symm

lemma vertex2_overlap : edge02 (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₁ =
      edge12 hcof hfib P ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₁ :=
  (edge02_one hcof hfib P).trans (edge12_one hcof hfib P).symm

abbrev constantZero : Paths (Paths (base (C := C))) ⥤ target (C := C) hcof hfib (P ⊗ interval) :=
  OrdinaryBarFreeResolutionFaces.faceZero hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (fst P interval)
abbrev constantOne : Paths (Paths (base (C := C))) ⥤ target (C := C) hcof hfib (P ⊗ interval) :=
  OrdinaryBarFreeResolutionFaces.faceOne hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (fst P interval)

lemma degeneracyZero_edge01 : FreePathResolutionDegreeTwo.degeneracyZero (base (C := C)) ⋙
    edge01 hcof hfib P = OrdinaryBarFreeResolutionComparison.comparison hcof hfib P := by
  rw [edge01, ← CategoryTheory.Functor.assoc,
    FreePathResolutionDegreeTwo.degeneracyZero_faceZero, CategoryTheory.Functor.id_comp]

lemma degeneracyZero_edge02 : FreePathResolutionDegreeTwo.degeneracyZero (base (C := C)) ⋙
    edge02 hcof hfib P = OrdinaryBarFreeResolutionComparison.comparison hcof hfib P := by
  rw [edge02, ← CategoryTheory.Functor.assoc,
    FreePathResolutionDegreeTwo.degeneracyZero_faceOne, CategoryTheory.Functor.id_comp]

lemma degeneracyZero_edge12 : FreePathResolutionDegreeTwo.degeneracyZero (base (C := C)) ⋙
    edge12 hcof hfib P = constantOne hcof hfib P := by
  rw [edge12, ← CategoryTheory.Functor.assoc,
    FreePathResolutionDegreeTwo.degeneracyZero_faceTwo, CategoryTheory.Functor.assoc,
    OrdinaryBarFreeResolutionComparison.comparison_degeneracy]
  rfl

lemma degeneracyOne_edge01 : FreePathResolutionDegreeTwo.degeneracyOne (base (C := C)) ⋙
    edge01 hcof hfib P = constantZero hcof hfib P := by
  rw [edge01, ← CategoryTheory.Functor.assoc,
    FreePathResolutionDegreeTwo.degeneracyOne_faceZero, CategoryTheory.Functor.assoc,
    OrdinaryBarFreeResolutionComparison.comparison_degeneracy]
  rfl

lemma degeneracyOne_edge02 : FreePathResolutionDegreeTwo.degeneracyOne (base (C := C)) ⋙
    edge02 hcof hfib P = OrdinaryBarFreeResolutionComparison.comparison hcof hfib P := by
  rw [edge02, ← CategoryTheory.Functor.assoc,
    FreePathResolutionDegreeTwo.degeneracyOne_faceOne, CategoryTheory.Functor.id_comp]

lemma degeneracyOne_edge12 : FreePathResolutionDegreeTwo.degeneracyOne (base (C := C)) ⋙
    edge12 hcof hfib P = OrdinaryBarFreeResolutionComparison.comparison hcof hfib P := by
  rw [edge12, ← CategoryTheory.Functor.assoc,
    FreePathResolutionDegreeTwo.degeneracyOne_faceTwo, CategoryTheory.Functor.id_comp]

lemma double_degeneracy_edge01 :
    (FreePathResolution.duplicate (base (C := C)) ⋙
      FreePathResolutionDegreeTwo.degeneracyZero (base (C := C))) ⋙ edge01 hcof hfib P =
        freeCover hcof hfib P ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib (fst P interval) := by
  rw [CategoryTheory.Functor.assoc, degeneracyZero_edge01,
    OrdinaryBarFreeResolutionComparison.comparison_degeneracy]

lemma double_degeneracy_edge02 :
    (FreePathResolution.duplicate (base (C := C)) ⋙
      FreePathResolutionDegreeTwo.degeneracyZero (base (C := C))) ⋙ edge02 hcof hfib P =
        freeCover hcof hfib P ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib (fst P interval) := by
  rw [CategoryTheory.Functor.assoc, degeneracyZero_edge02,
    OrdinaryBarFreeResolutionComparison.comparison_degeneracy]

lemma double_degeneracy_edge12 :
    (FreePathResolution.duplicate (base (C := C)) ⋙
      FreePathResolutionDegreeTwo.degeneracyZero (base (C := C))) ⋙ edge12 hcof hfib P =
        freeCover hcof hfib P ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib (fst P interval) := by
  rw [FreePathResolutionDegreeTwo.degeneracy_overlap, CategoryTheory.Functor.assoc,
    degeneracyOne_edge12, OrdinaryBarFreeResolutionComparison.comparison_degeneracy]

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeTriangleBoundary
