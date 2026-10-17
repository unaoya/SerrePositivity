module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeTriangleDegeneracy

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFreeTriangleFiller

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：A two-simplex filler preserving both whole degeneracy images。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0193][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0193
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A two-simplex filler preserving both whole degeneracy images

The fixed generators are the union of the two actual degeneracy images.
Their prescribed values agree on the exact intersection, and each restricts
to the already constructed boundary. The relative free extension therefore
retains the entire boundary and both degenerate triangles.
-/

@[expose] public section
universe v u r
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeTriangleFiller
open OrdinaryBarFreeDiagramExtension OrdinaryBarFreeTriangleDegeneracy
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})

abbrev D := Cᵒᵖ × C
abbrev parameters (Q : SSet.{r}) := Q ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 2)
abbrev boundaryGenerators := OrdinaryBarFreeTriangleGluing.generators (C := C) hcof hfib P

variable {X Y : D (C := C)} (e : Quiver.Path (V := Paths (D (C := C))) X Y)

def Left : Prop := ∃ q : Quiver.Path X Y, e = Quiver.Hom.toPath (V := Paths (D (C := C))) q
def Right : Prop := ∃ p : Quiver.Path X Y, e = (FreePathResolution.duplicate (D (C := C))).map p

def recover : Quiver.Path X Y := (FreePathResolution.counit (Paths (D (C := C)))).map e

def valueLeft :
    liftedObject hcof hfib (T := parameters P) ((boundaryGenerators hcof hfib P).obj X) ⟶
    liftedObject hcof hfib (T := parameters P) ((boundaryGenerators hcof hfib P).obj Y) :=
  (triangle hcof hfib P 1).map (Quiver.Hom.toPath (V := Paths (D (C := C))) (recover e))

def valueRight :
    liftedObject hcof hfib (T := parameters P) ((boundaryGenerators hcof hfib P).obj X) ⟶
    liftedObject hcof hfib (T := parameters P) ((boundaryGenerators hcof hfib P).obj Y) :=
  (triangle hcof hfib P 0).map (Quiver.Hom.toPath (V := Paths (D (C := C))) (recover e))

lemma values_agree (hl : Left e) (hr : Right e) :
    valueLeft hcof hfib P e = valueRight hcof hfib P e := by
  obtain ⟨q, hq⟩ := hl
  obtain ⟨p, hp⟩ := hr
  obtain ⟨f, rfl, rfl⟩ :=
    (FreePathDegeneracyImage.generator_image_intersection p q).mp (hq.symm.trans hp)
  subst e
  have h := congr($(triangle_duplicate_equal (C := C) hcof hfib P).map f.toPath)
  simpa only [valueLeft, valueRight, recover, CategoryTheory.Functor.comp_map,
    FreePathResolution.duplicate_generator, FreePathResolution.counit, pathComposition_map,
    composePath_toPath] using h

def value : liftedObject hcof hfib (T := parameters P)
    ((boundaryGenerators hcof hfib P).obj X) ⟶
      liftedObject hcof hfib (T := parameters P) ((boundaryGenerators hcof hfib P).obj Y) := by
  classical
  exact if Left e then valueLeft hcof hfib P e else valueRight hcof hfib P e

lemma value_left (h : Left e) : value hcof hfib P e = valueLeft hcof hfib P e := by
  classical
  exact ite_eq_left h

lemma value_right (h : Right e) : value hcof hfib P e = valueRight hcof hfib P e := by
  classical
  by_cases hl : Left e
  · exact (value_left hcof hfib P e hl).trans (values_agree hcof hfib P e hl h)
  · exact ite_eq_right hl

lemma restriction_left (h : Left e) :
    (OrdinaryBarChoiceCategory.reindex hcof hfib (inclusion P)).map (valueLeft hcof hfib P e) =
      (boundaryGenerators hcof hfib P).map e := by
  obtain ⟨q, rfl⟩ := h
  have hh := congr($(boundary_degeneracyZero (C := C) hcof hfib P).map
    (Quiver.Hom.toPath (V := Paths (D (C := C))) q))
  simpa only [valueLeft, recover, CategoryTheory.Functor.comp_map,
    FreePathResolution.duplicate_generator, FreePathResolution.counit, pathComposition_map,
    composePath_toPath, OrdinaryBarFreeTriangleGluing.boundary, Paths.lift_toPath] using hh.symm

lemma restriction_right (h : Right e) :
    (OrdinaryBarChoiceCategory.reindex hcof hfib (inclusion P)).map (valueRight hcof hfib P e) =
      (boundaryGenerators hcof hfib P).map e := by
  obtain ⟨p, rfl⟩ := h
  have hh := congr($(boundary_degeneracyOne (C := C) hcof hfib P).map
    (Quiver.Hom.toPath (V := Paths (D (C := C))) p))
  simpa only [valueRight, recover, FreePathDegeneracyImage.counit_duplicate,
    CategoryTheory.Functor.comp_map, FreePathResolution.map_generator,
    OrdinaryBarFreeTriangleGluing.boundary, Paths.lift_toPath] using hh.symm

def prescribed : OrdinaryBarRelativeFreeDiagramExtension.Prescribed hcof hfib
    (inclusion P) (boundaryGenerators (C := C) hcof hfib P) where
  fixed e := Left e ∨ Right e
  value e _ := value hcof hfib P e
  restriction e he := by
    rcases he with hl | hr
    · rw [value_left hcof hfib P e hl]
      exact restriction_left hcof hfib P e hl
    · rw [value_right hcof hfib P e hr]
      exact restriction_right hcof hfib P e hr

def filler : Paths (Paths (Paths (D (C := C)))) ⥤ target (C := C) hcof hfib (parameters P) :=
  OrdinaryBarRelativeFreeDiagramExtension.extend hcof hfib (inclusion P)
    (boundaryGenerators hcof hfib P) (prescribed hcof hfib P)

lemma filler_boundary : filler (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (inclusion P) =
      OrdinaryBarFreeTriangleGluing.boundary hcof hfib P :=
  OrdinaryBarRelativeFreeDiagramExtension.extend_restriction hcof hfib _ _ _

lemma filler_face0 : filler (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.δ (0 : Fin 3)) =
      OrdinaryBarFreeTriangleBoundary.edge12 hcof hfib P := by
  rw [← SSet.boundary.ι_ι (0 : Fin 3), whiskerLeft_comp,
    OrdinaryBarChoiceCategory.reindex_comp, ← CategoryTheory.Functor.assoc,
    filler_boundary, OrdinaryBarFreeTriangleGluing.boundary_face0]

lemma filler_face1 : filler (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.δ (1 : Fin 3)) =
      OrdinaryBarFreeTriangleBoundary.edge02 hcof hfib P := by
  rw [← SSet.boundary.ι_ι (1 : Fin 3), whiskerLeft_comp,
    OrdinaryBarChoiceCategory.reindex_comp, ← CategoryTheory.Functor.assoc,
    filler_boundary, OrdinaryBarFreeTriangleGluing.boundary_face1]

lemma filler_face2 : filler (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.δ (2 : Fin 3)) =
      OrdinaryBarFreeTriangleBoundary.edge01 hcof hfib P := by
  rw [← SSet.boundary.ι_ι (2 : Fin 3), whiskerLeft_comp,
    OrdinaryBarChoiceCategory.reindex_comp, ← CategoryTheory.Functor.assoc,
    filler_boundary, OrdinaryBarFreeTriangleGluing.boundary_face2]

lemma filler_fixed_left (h : Left e) : (filler hcof hfib P).map
    (Quiver.Hom.toPath (V := Paths (Paths (D (C := C)))) e) =
    valueLeft hcof hfib P e := by
  unfold filler
  rw [OrdinaryBarRelativeFreeDiagramExtension.extend_fixed hcof hfib
    (inclusion P) (boundaryGenerators hcof hfib P) (prescribed hcof hfib P) e (Or.inl h)]
  exact value_left hcof hfib P e h

lemma filler_fixed_right (h : Right e) : (filler hcof hfib P).map
    (Quiver.Hom.toPath (V := Paths (Paths (D (C := C)))) e) =
    valueRight hcof hfib P e := by
  unfold filler
  rw [OrdinaryBarRelativeFreeDiagramExtension.extend_fixed hcof hfib
    (inclusion P) (boundaryGenerators hcof hfib P) (prescribed hcof hfib P) e (Or.inr h)]
  exact value_right hcof hfib P e h

lemma filler_degeneracyZero : FreePathResolutionDegreeTwo.degeneracyZero (D (C := C)) ⋙
    filler hcof hfib P = triangle hcof hfib P 1 := by
  refine Paths.ext_functor
    (F := FreePathResolutionDegreeTwo.degeneracyZero (D (C := C)) ⋙ filler hcof hfib P)
    (G := triangle hcof hfib P 1) rfl ?_
  intro X Y q
  simp only [CategoryTheory.Functor.comp_map, FreePathResolution.duplicate_generator,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [filler_fixed_left hcof hfib P _ ⟨q, rfl⟩]
  simp only [valueLeft, recover, FreePathResolution.counit, pathComposition_map, composePath_toPath]

lemma filler_degeneracyOne : FreePathResolutionDegreeTwo.degeneracyOne (D (C := C)) ⋙
    filler hcof hfib P = triangle hcof hfib P 0 := by
  refine Paths.ext_functor
    (F := FreePathResolutionDegreeTwo.degeneracyOne (D (C := C)) ⋙ filler hcof hfib P)
    (G := triangle hcof hfib P 0) rfl ?_
  intro X Y p
  simp only [CategoryTheory.Functor.comp_map, FreePathResolution.map_generator,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [filler_fixed_right hcof hfib P _ ⟨p, rfl⟩]
  simp only [valueRight, recover, FreePathDegeneracyImage.counit_duplicate]

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeTriangleFiller
