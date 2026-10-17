module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleGluing
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryExt
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreePathDegeneracyImage
public import SerrePositivity.HomotopicalAlgebra.Simplicial.TriangleDegeneracyParameters

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFreeTriangleDegeneracy

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Prescribed degenerate triangles restrict to the actual glued boundary。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0192][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0192
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Prescribed degenerate triangles restrict to the actual glued boundary

These equalities compare whole boundary functors. Together with the exact
intersection of generator images they supply the relative input for a
subsequent two-simplex extension; that extension is not assumed here.
-/

@[expose] public section
universe v u r
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeTriangleDegeneracy
open OrdinaryBarFreeTriangleBoundary TriangleDegeneracyParameters
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})

abbrev inclusion (Q : SSet.{r}) := Q ◁ (SSet.boundary 2).ι
abbrev facet (Q : SSet.{r}) (k : Fin 3) := Q ◁ SSet.boundary.ι k

def triangle (i : Fin 2) : Paths (Paths (Cᵒᵖ × C)) ⥤
    OrdinaryBarFreeDiagramExtension.target (C := C) hcof hfib
      (P ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 2)) :=
  OrdinaryBarFreeResolutionComparison.comparison hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ sigma i)

lemma triangle_duplicate (i : Fin 2) : FreePathResolution.duplicate (Cᵒᵖ × C) ⋙
    triangle hcof hfib P i = OrdinaryBarFreeDiagramExtension.freeCover hcof hfib P ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib
        (fst P (SSet.stdSimplex.obj (SimplexCategory.mk 2))) := by
  rw [triangle, ← CategoryTheory.Functor.assoc,
    OrdinaryBarFreeResolutionComparison.comparison_degeneracy, CategoryTheory.Functor.assoc,
    ← OrdinaryBarChoiceCategory.reindex_comp, whiskerLeft_fst]

lemma triangle_duplicate_equal : FreePathResolution.duplicate (Cᵒᵖ × C) ⋙
    triangle hcof hfib P 1 = FreePathResolution.duplicate (Cᵒᵖ × C) ⋙ triangle hcof hfib P 0 :=
  (triangle_duplicate hcof hfib P 1).trans (triangle_duplicate hcof hfib P 0).symm

lemma reindex_face (i : Fin 2) (k : Fin 3) :
    (OrdinaryBarChoiceCategory.reindex (C := C) hcof hfib (P ◁ sigma i) ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib (inclusion P)) ⋙
        OrdinaryBarChoiceCategory.reindex hcof hfib (facet P k) =
      OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ (SSet.stdSimplex.δ k ≫ sigma i)) := by
  rw [CategoryTheory.Functor.assoc, ← OrdinaryBarChoiceCategory.reindex_comp,
    ← OrdinaryBarChoiceCategory.reindex_comp]
  congr 1

lemma triangle_face (i : Fin 2) (k : Fin 3) :
    (triangle (C := C) hcof hfib P i ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib (inclusion P)) ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib (facet P k) =
    OrdinaryBarFreeResolutionComparison.comparison hcof hfib P ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ (SSet.stdSimplex.δ k ≫ sigma i)) := by
  change OrdinaryBarFreeResolutionComparison.comparison hcof hfib P ⋙
    ((OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ sigma i) ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib (inclusion P)) ⋙
        OrdinaryBarChoiceCategory.reindex hcof hfib (facet P k)) = _
  rw [reindex_face]

abbrev zeroFaces : Fin 3 →
    (Paths (Paths (Cᵒᵖ × C)) ⥤ OrdinaryBarFreeDiagramExtension.target (C := C) hcof hfib
    (P ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 1))) :=
  ![constantOne (C := C) hcof hfib P,
    OrdinaryBarFreeResolutionComparison.comparison (C := C) hcof hfib P,
    OrdinaryBarFreeResolutionComparison.comparison (C := C) hcof hfib P]
abbrev oneFaces : Fin 3 →
    (Paths (Paths (Cᵒᵖ × C)) ⥤ OrdinaryBarFreeDiagramExtension.target (C := C) hcof hfib
    (P ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 1))) :=
  ![OrdinaryBarFreeResolutionComparison.comparison (C := C) hcof hfib P,
    OrdinaryBarFreeResolutionComparison.comparison (C := C) hcof hfib P,
    constantZero (C := C) hcof hfib P]

lemma triangleZero_face (k : Fin 3) :
    (triangle (C := C) hcof hfib P 1 ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib (inclusion P)) ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib (facet P k) = zeroFaces hcof hfib P k := by
  rw [triangle_face]
  fin_cases k
  · change OrdinaryBarFreeResolutionComparison.comparison (C := C) hcof hfib P ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ (SSet.stdSimplex.δ (0 : Fin 3) ≫
        sigma 1)) = _
    rw [face0_sigma1.{max u v}, tensor_const_one, OrdinaryBarChoiceCategory.reindex_comp,
      ← CategoryTheory.Functor.assoc, OrdinaryBarFreeResolutionComparison.comparison_one]
    rfl
  · change OrdinaryBarFreeResolutionComparison.comparison (C := C) hcof hfib P ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ (SSet.stdSimplex.δ (1 : Fin 3) ≫
        sigma 1)) = _
    rw [face1_sigma1.{max u v}, MonoidalCategory.whiskerLeft_id,
      OrdinaryBarChoiceCategory.reindex_id,
      CategoryTheory.Functor.comp_id]
    rfl
  · change OrdinaryBarFreeResolutionComparison.comparison (C := C) hcof hfib P ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ (SSet.stdSimplex.δ (2 : Fin 3) ≫
        sigma 1)) = _
    rw [face2_sigma1.{max u v}, MonoidalCategory.whiskerLeft_id,
      OrdinaryBarChoiceCategory.reindex_id,
      CategoryTheory.Functor.comp_id]
    rfl

lemma triangleOne_face (k : Fin 3) :
    (triangle (C := C) hcof hfib P 0 ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib (inclusion P)) ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib (facet P k) = oneFaces hcof hfib P k := by
  rw [triangle_face]
  fin_cases k
  · change OrdinaryBarFreeResolutionComparison.comparison (C := C) hcof hfib P ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ (SSet.stdSimplex.δ (0 : Fin 3) ≫
        sigma 0)) = _
    rw [face0_sigma0.{max u v}, MonoidalCategory.whiskerLeft_id,
      OrdinaryBarChoiceCategory.reindex_id,
      CategoryTheory.Functor.comp_id]
    rfl
  · change OrdinaryBarFreeResolutionComparison.comparison (C := C) hcof hfib P ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ (SSet.stdSimplex.δ (1 : Fin 3) ≫
        sigma 0)) = _
    rw [face1_sigma0.{max u v}, MonoidalCategory.whiskerLeft_id,
      OrdinaryBarChoiceCategory.reindex_id,
      CategoryTheory.Functor.comp_id]
    rfl
  · change OrdinaryBarFreeResolutionComparison.comparison (C := C) hcof hfib P ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ (SSet.stdSimplex.δ (2 : Fin 3) ≫
        sigma 0)) = _
    rw [face2_sigma0.{max u v}, tensor_const_zero, OrdinaryBarChoiceCategory.reindex_comp,
      ← CategoryTheory.Functor.assoc, OrdinaryBarFreeResolutionComparison.comparison_zero]
    rfl

lemma boundary_degeneracyZero : FreePathResolutionDegreeTwo.degeneracyZero (Cᵒᵖ × C) ⋙
    OrdinaryBarFreeTriangleGluing.boundary hcof hfib P = triangle hcof hfib P 1 ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib (inclusion P) := by
  refine Paths.ext_functor (F := FreePathResolutionDegreeTwo.degeneracyZero (Cᵒᵖ × C) ⋙
    OrdinaryBarFreeTriangleGluing.boundary hcof hfib P)
    (G := triangle hcof hfib P 1 ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib (inclusion P))
    rfl ?_
  intro X Y e
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply OrdinaryBarChoiceBoundaryExt.hom_ext hcof hfib
  intro k
  have hk : (FreePathResolutionDegreeTwo.degeneracyZero (Cᵒᵖ × C) ⋙
      OrdinaryBarFreeTriangleGluing.boundary hcof hfib P) ⋙
        OrdinaryBarChoiceCategory.reindex hcof hfib (facet P k) =
      (triangle hcof hfib P 1 ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib (inclusion P)) ⋙
        OrdinaryBarChoiceCategory.reindex hcof hfib (facet P k) := by
    rw [triangleZero_face, CategoryTheory.Functor.assoc]
    fin_cases k
    · change FreePathResolutionDegreeTwo.degeneracyZero (Cᵒᵖ × C) ⋙
        (OrdinaryBarFreeTriangleGluing.boundary hcof hfib P ⋙
          OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι (0 : Fin 3))) = _
      rw [OrdinaryBarFreeTriangleGluing.boundary_face0 (C := C) hcof hfib P,
        degeneracyZero_edge12]; rfl
    · change FreePathResolutionDegreeTwo.degeneracyZero (Cᵒᵖ × C) ⋙
        (OrdinaryBarFreeTriangleGluing.boundary hcof hfib P ⋙
          OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι (1 : Fin 3))) = _
      rw [OrdinaryBarFreeTriangleGluing.boundary_face1 (C := C) hcof hfib P,
        degeneracyZero_edge02]; rfl
    · change FreePathResolutionDegreeTwo.degeneracyZero (Cᵒᵖ × C) ⋙
        (OrdinaryBarFreeTriangleGluing.boundary hcof hfib P ⋙
          OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι (2 : Fin 3))) = _
      rw [OrdinaryBarFreeTriangleGluing.boundary_face2 (C := C) hcof hfib P,
        degeneracyZero_edge01]; rfl
  exact congr($(hk).map e.toPath)

lemma boundary_degeneracyOne : FreePathResolutionDegreeTwo.degeneracyOne (Cᵒᵖ × C) ⋙
    OrdinaryBarFreeTriangleGluing.boundary hcof hfib P = triangle hcof hfib P 0 ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib (inclusion P) := by
  refine Paths.ext_functor (F := FreePathResolutionDegreeTwo.degeneracyOne (Cᵒᵖ × C) ⋙
    OrdinaryBarFreeTriangleGluing.boundary hcof hfib P)
    (G := triangle hcof hfib P 0 ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib (inclusion P))
    rfl ?_
  intro X Y e
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply OrdinaryBarChoiceBoundaryExt.hom_ext hcof hfib
  intro k
  have hk : (FreePathResolutionDegreeTwo.degeneracyOne (Cᵒᵖ × C) ⋙
      OrdinaryBarFreeTriangleGluing.boundary hcof hfib P) ⋙
        OrdinaryBarChoiceCategory.reindex hcof hfib (facet P k) =
      (triangle hcof hfib P 0 ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib (inclusion P)) ⋙
        OrdinaryBarChoiceCategory.reindex hcof hfib (facet P k) := by
    rw [triangleOne_face, CategoryTheory.Functor.assoc]
    fin_cases k
    · change FreePathResolutionDegreeTwo.degeneracyOne (Cᵒᵖ × C) ⋙
        (OrdinaryBarFreeTriangleGluing.boundary hcof hfib P ⋙
          OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι (0 : Fin 3))) = _
      rw [OrdinaryBarFreeTriangleGluing.boundary_face0 (C := C) hcof hfib P,
        degeneracyOne_edge12]; rfl
    · change FreePathResolutionDegreeTwo.degeneracyOne (Cᵒᵖ × C) ⋙
        (OrdinaryBarFreeTriangleGluing.boundary hcof hfib P ⋙
          OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι (1 : Fin 3))) = _
      rw [OrdinaryBarFreeTriangleGluing.boundary_face1 (C := C) hcof hfib P,
        degeneracyOne_edge02]; rfl
    · change FreePathResolutionDegreeTwo.degeneracyOne (Cᵒᵖ × C) ⋙
        (OrdinaryBarFreeTriangleGluing.boundary hcof hfib P ⋙
          OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι (2 : Fin 3))) = _
      rw [OrdinaryBarFreeTriangleGluing.boundary_face2 (C := C) hcof hfib P,
        degeneracyOne_edge01]; rfl
  exact congr($(hk).map e.toPath)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeTriangleDegeneracy
