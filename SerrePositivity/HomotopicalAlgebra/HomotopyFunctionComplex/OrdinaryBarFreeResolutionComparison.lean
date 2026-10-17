module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeDiagramHomotopy
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionFaces

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFreeResolutionComparison

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The first free-resolution comparison, constant on the entire degeneracy image。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0181][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0181
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The first free-resolution comparison, constant on the entire degeneracy image

Both endpoints are the actual free-cover faces. The comparison retains
arbitrary existing parameters and is a strict functor on the double free
category. This constructs the first comparison, not all higher coherence.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionComparison
open OrdinaryBarFreeDiagramExtension OrdinaryBarFreeResolutionFaces
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})

def startGenerators : Paths (Cᵒᵖ × C) ⥤q target (C := C) hcof hfib P :=
  Paths.of _ ⋙q (faceZero hcof hfib P).toPrefunctor

def endData : OrdinaryBarFreeDiagramHomotopy.End hcof hfib
    (startGenerators (C := C) hcof hfib P) where
  extension e := ((faceOne hcof hfib P).map e.toPath).extension ≫
    OrdinaryBarChoiceComposition.relabel hcof hfib (by
      have h := congr($(projection_equal (C := C) hcof hfib P).map e.toPath)
      exact h.symm)

lemma faceZero_singleton {X Y : Cᵒᵖ × C} (f : X ⟶ Y) :
    (faceZero hcof hfib P).map (Quiver.Hom.toPath (V := Paths (Cᵒᵖ × C)) f.toPath) =
      (freeCover hcof hfib P).map f.toPath := by
  have h := congr($(degeneracy_faceZero (C := C) hcof hfib P).map f.toPath)
  simpa only [CategoryTheory.Functor.comp_map, FreePathResolution.duplicate_generator] using h

lemma faceOne_singleton {X Y : Cᵒᵖ × C} (f : X ⟶ Y) :
    (faceOne hcof hfib P).map (Quiver.Hom.toPath (V := Paths (Cᵒᵖ × C)) f.toPath) =
      (freeCover hcof hfib P).map f.toPath := by
  have h := congr($(degeneracy_faceOne (C := C) hcof hfib P).map f.toPath)
  simpa only [CategoryTheory.Functor.comp_map, FreePathResolution.duplicate_generator] using h

def IsSingleton {X Y : Cᵒᵖ × C} (p : Quiver.Path X Y) : Prop := ∃ f : X ⟶ Y, p = f.toPath

def fixed : OrdinaryBarFreeDiagramHomotopy.Fixed hcof hfib
    (startGenerators (C := C) hcof hfib P) (endData (C := C) hcof hfib P) where
  predicate p := IsSingleton p
  agree p hp := by
    obtain ⟨f, rfl⟩ := hp
    exact OrdinaryBarFreeDiagramHomotopy.extension_eq hcof hfib _ _
      ((faceOne_singleton hcof hfib P f).trans (faceZero_singleton hcof hfib P f).symm) _

def comparison : Paths (Paths (Cᵒᵖ × C)) ⥤ target (C := C) hcof hfib
    (P ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 1)) :=
  OrdinaryBarFreeDiagramHomotopy.comparison (C := C) hcof hfib
    (startGenerators (C := C) hcof hfib P)
    (endData (C := C) hcof hfib P) (fixed (C := C) hcof hfib P)

lemma comparison_zero : comparison (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₀ = faceZero hcof hfib P := by
  rw [comparison, OrdinaryBarFreeDiagramHomotopy.comparison_zero]
  exact (Paths.lift_unique _ (faceZero hcof hfib P) rfl).symm

lemma comparison_one : comparison (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₁ = faceOne hcof hfib P := by
  rw [comparison, OrdinaryBarFreeDiagramHomotopy.comparison_one]
  refine Paths.ext_functor
    (F := Paths.lift (OrdinaryBarFreeDiagramHomotopy.endGenerators hcof hfib
      (startGenerators (C := C) hcof hfib P) (endData (C := C) hcof hfib P)))
    (G := faceOne hcof hfib P) rfl ?_
  intro X Y e
  simp only [Paths.lift_toPath, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact OrdinaryBarFreeDiagramHomotopy.normalized_eq hcof hfib
    ((faceZero hcof hfib P).map e.toPath) ((faceOne hcof hfib P).map e.toPath) _

lemma comparison_degeneracy : FreePathResolution.duplicate (Cᵒᵖ × C) ⋙
    comparison (C := C) hcof hfib P = freeCover hcof hfib P ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib
        (fst P (SSet.stdSimplex.obj (SimplexCategory.mk 1))) := by
  refine Paths.ext_functor (F := FreePathResolution.duplicate (Cᵒᵖ × C) ⋙
    comparison (C := C) hcof hfib P) (G := freeCover hcof hfib P ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib
        (fst P (SSet.stdSimplex.obj (SimplexCategory.mk 1)))) rfl ?_
  intro X Y f
  simp only [CategoryTheory.Functor.comp_map, FreePathResolution.duplicate_generator,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  change (OrdinaryBarFreeDiagramHomotopy.comparison (C := C) hcof hfib _ _ _).map
    (Quiver.Hom.toPath (V := Paths (Cᵒᵖ × C)) f.toPath) = _
  rw [OrdinaryBarFreeDiagramHomotopy.comparison_fixed hcof hfib
    (startGenerators (C := C) hcof hfib P) (endData (C := C) hcof hfib P)
    (fixed (C := C) hcof hfib P) f.toPath ⟨f, rfl⟩]
  exact congrArg (fun a => (OrdinaryBarChoiceCategory.reindex hcof hfib
    (fst P (SSet.stdSimplex.obj (SimplexCategory.mk 1)))).map a)
      (faceZero_singleton hcof hfib P f)

lemma comparison_projection : comparison (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.projection hcof hfib _ =
      faceZero hcof hfib P ⋙ OrdinaryBarChoiceCategory.projection hcof hfib P := by
  have h := congrArg (fun F => F ⋙ OrdinaryBarChoiceCategory.projection (C := C) hcof hfib P)
    (comparison_zero hcof hfib P)
  simpa only [CategoryTheory.Functor.assoc, OrdinaryBarChoiceCategory.reindex_projection] using h

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionComparison
