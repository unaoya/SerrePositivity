module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegenerateBoundary
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeDegeneracyExtension

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFreeResolutionStep

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Raise the degree of the coherent free choice diagram。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0188][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0188
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Raise the degree of the coherent free choice diagram

Two consecutive choice functors satisfying the lower face and degeneracy
equations determine a next functor satisfying every required face and
degeneracy equation. The overlap and boundary restrictions are derived,
rather than supplied as extra assumptions to the relative filler.
-/

@[expose] public section
universe v u vD uD r
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionStep
open FreeGeneratorCategories FreeGeneratorDegeneracies OrdinaryBarFreeDiagramExtension
open OrdinaryBarChoiceBoundaryGluing OrdinaryBarFreeResolutionDegeneracyValues

abbrev inclusion (n : ℕ) (P : SSet.{r}) := P ◁ (SSet.boundary (n + 2)).ι

variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (D : Type uD) [Category.{vD} D] (n : ℕ) (P : SSet.{max u v})
  (F : degree D (n + 2) ⥤ target (C := C) hcof hfib (parameters P (n + 1)))
  (G : degree D (n + 1) ⥤ target (C := C) hcof hfib (parameters P n))
  (faceLaw : ∀ i : Fin (n + 2), F ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.δ i) =
      FreeGeneratorFaces.fixedFace D (n + 1) i ⋙ G)
  (degeneracyLaw : ∀ i : Fin (n + 1), degeneracyFunctor D n i ⋙ F =
    G ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma n i))

abbrev boundaryDiagram := OrdinaryBarFreeResolutionBoundary.boundary hcof hfib D n P F G faceLaw

def boundaryGenerators : degree D (n + 2) ⥤q
    target (C := C) hcof hfib (P ⊗ (SSet.boundary (n + 2)).toSSet) :=
  Paths.of (degree D (n + 2)) ⋙q (boundaryDiagram hcof hfib D n P F G faceLaw).toPrefunctor

include degeneracyLaw in
lemma value_restriction (i : Fin (n + 2)) {X Y : D} (p : hom (n + 1) X Y) :
    (OrdinaryBarChoiceCategory.reindex hcof hfib (inclusion n P)).map
      (value hcof hfib D n P F i p) =
    (boundaryGenerators hcof hfib D n P F G faceLaw).map (degeneracy (n + 1) i p) := by
  change (OrdinaryBarChoiceCategory.reindex hcof hfib (inclusion n P)).map
      ((diagram hcof hfib D n P F i).map (singleton (n + 1) p)) =
    (boundaryDiagram hcof hfib D n P F G faceLaw).map
      (singleton (n + 2) (degeneracy (n + 1) i p))
  have hh := congr($(OrdinaryBarFreeResolutionDegenerateBoundary.boundary_degeneracy
    hcof hfib D n P F G faceLaw degeneracyLaw i).map (singleton (n + 1) p))
  simpa only [CategoryTheory.Functor.comp_map, degeneracyFunctor_generator] using hh.symm

def filler : degree D (n + 3) ⥤ target (C := C) hcof hfib (parameters P (n + 2)) :=
  OrdinaryBarFreeDegeneracyExtension.filler hcof hfib D n (inclusion n P)
    (boundaryGenerators hcof hfib D n P F G faceLaw) (value hcof hfib D n P F)
    (value_restriction hcof hfib D n P F G faceLaw degeneracyLaw)

lemma filler_boundary : filler hcof hfib D n P F G faceLaw degeneracyLaw ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (inclusion n P) =
      boundaryDiagram hcof hfib D n P F G faceLaw := by
  rw [filler, OrdinaryBarFreeDegeneracyExtension.filler_boundary]
  exact (Paths.lift_unique (V := degree D (n + 2)) _
    (boundaryDiagram hcof hfib D n P F G faceLaw) rfl).symm

lemma filler_face (k : Fin (n + 3)) : filler hcof hfib D n P F G faceLaw degeneracyLaw ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.δ k) =
      FreeGeneratorFaces.fixedFace D (n + 2) k ⋙ F := by
  rw [← SSet.boundary.ι_ι k, whiskerLeft_comp, OrdinaryBarChoiceCategory.reindex_comp,
    ← CategoryTheory.Functor.assoc]
  change (filler hcof hfib D n P F G faceLaw degeneracyLaw ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (inclusion n P)) ⋙ _ = _
  rw [filler_boundary]
  exact OrdinaryBarFreeResolutionBoundary.boundary_face hcof hfib D n P F G faceLaw k

lemma filler_degeneracy (i : Fin (n + 2)) : degeneracyFunctor D (n + 1) i ⋙
    filler hcof hfib D n P F G faceLaw degeneracyLaw =
      F ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma (n + 1) i) := by
  rw [filler, OrdinaryBarFreeDegeneracyExtension.filler_degeneracy hcof hfib D n _ _ _
    (values_compatible hcof hfib D n P F G degeneracyLaw) _ i]
  exact diagram_from_generators hcof hfib D n P F i

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionStep
