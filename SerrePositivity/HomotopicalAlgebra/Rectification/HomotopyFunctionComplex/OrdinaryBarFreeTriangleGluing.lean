module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarChoiceTriangleGluing
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeTriangleBoundary

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFreeTriangleGluing

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual free triangle boundary diagram with all original parameters。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0194][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0194
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual free triangle boundary diagram with all original parameters

The three previously constructed edges glue to a strict functor on the
triple free category with parameter P times the actual boundary of the
standard two-simplex. No relative two-simplex filler is claimed here.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeTriangleGluing
open OrdinaryBarFreeDiagramExtension OrdinaryBarFreeTriangleBoundary
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})

abbrev edgeA {X Y : Paths (Paths (Cᵒᵖ × C))} (e : X ⟶ Y) :=
  (edge01 (C := C) hcof hfib P).map e.toPath
abbrev edgeB {X Y : Paths (Paths (Cᵒᵖ × C))} (e : X ⟶ Y) :=
  (edge02 (C := C) hcof hfib P).map e.toPath
abbrev edgeC {X Y : Paths (Paths (Cᵒᵖ × C))} (e : X ⟶ Y) :=
  (edge12 (C := C) hcof hfib P).map e.toPath

lemma overlap0 {X Y : Paths (Paths (Cᵒᵖ × C))} (e : X ⟶ Y) :
    (OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₀).map (edgeA hcof hfib P e) =
      (OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₀).map (edgeB hcof hfib P e) :=
  congr($(vertex0_overlap (C := C) hcof hfib P).map e.toPath)

lemma overlap1 {X Y : Paths (Paths (Cᵒᵖ × C))} (e : X ⟶ Y) :
    (OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₁).map (edgeA hcof hfib P e) =
      (OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₀).map (edgeC hcof hfib P e) :=
  congr($(vertex1_overlap (C := C) hcof hfib P).map e.toPath)

lemma overlap2 {X Y : Paths (Paths (Cᵒᵖ × C))} (e : X ⟶ Y) :
    (OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₁).map (edgeB hcof hfib P e) =
      (OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₁).map (edgeC hcof hfib P e) :=
  congr($(vertex2_overlap (C := C) hcof hfib P).map e.toPath)

def generators : Paths (Paths (Cᵒᵖ × C)) ⥤q target (C := C) hcof hfib
    (P ⊗ (SSet.boundary 2).toSSet) where
  obj X := OrdinaryBarChoiceTriangleGluing.boundaryObject hcof hfib ((edge01 hcof hfib P).obj X)
  map e := OrdinaryBarChoiceTriangleGluing.boundaryHom hcof hfib
    (edgeA hcof hfib P e) (edgeB hcof hfib P e) (edgeC hcof hfib P e)
    (overlap0 hcof hfib P e) (overlap1 hcof hfib P e) (overlap2 hcof hfib P e)

def boundary : source (C := C) ⥤ target (C := C) hcof hfib (P ⊗ (SSet.boundary 2).toSSet) :=
  Paths.lift (generators hcof hfib P)

lemma boundary_face2 : boundary (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι (2 : Fin 3)) =
      edge01 hcof hfib P := by
  refine Paths.ext_functor (F := boundary hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι (2 : Fin 3)))
    (G := edge01 hcof hfib P) rfl ?_
  intro X Y e
  simp only [CategoryTheory.Functor.comp_map, boundary, Paths.lift_toPath,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  exact OrdinaryBarChoiceTriangleGluing.boundaryHom_face2 hcof hfib _ _ _ _ _ _

lemma boundary_face1 : boundary (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι (1 : Fin 3)) =
      edge02 hcof hfib P := by
  refine Paths.ext_functor (F := boundary hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι (1 : Fin 3)))
    (G := edge02 hcof hfib P) rfl ?_
  intro X Y e
  simp only [CategoryTheory.Functor.comp_map, boundary, Paths.lift_toPath,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  exact OrdinaryBarChoiceTriangleGluing.boundaryHom_face1 hcof hfib _ _ _ _ _ _

lemma boundary_face0 : boundary (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι (0 : Fin 3)) =
      edge12 hcof hfib P := by
  refine Paths.ext_functor (F := boundary hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι (0 : Fin 3)))
    (G := edge12 hcof hfib P) rfl ?_
  intro X Y e
  simp only [CategoryTheory.Functor.comp_map, boundary, Paths.lift_toPath,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  exact OrdinaryBarChoiceTriangleGluing.boundaryHom_face0 hcof hfib _ _ _ _ _ _

lemma boundary_projection : boundary (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.projection hcof hfib _ =
      edge01 hcof hfib P ⋙ OrdinaryBarChoiceCategory.projection hcof hfib _ := by
  have h := congrArg (fun F => F ⋙ OrdinaryBarChoiceCategory.projection (C := C) hcof hfib _)
    (boundary_face2 hcof hfib P)
  simpa only [CategoryTheory.Functor.assoc, OrdinaryBarChoiceCategory.reindex_projection] using h

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeTriangleGluing
