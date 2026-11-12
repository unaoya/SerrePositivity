module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeResolutionMixedFaces
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryExt

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFreeResolutionDegenerateBoundary

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The prescribed all-degree degeneracies restrict to the actual boundary。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0183][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0183
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The prescribed all-degree degeneracies restrict to the actual boundary

Agreement on every facet follows from the mixed identities. Joint boundary
extensionality then gives equality of whole functors, without faithfulness
of any individual face restriction or of the base projection.
-/

@[expose] public section
universe v u vD uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegenerateBoundary
open FreeGeneratorCategories FreeGeneratorMixedOperators OrdinaryBarFreeDiagramExtension
open OrdinaryBarChoiceBoundaryGluing OrdinaryBarFreeResolutionDegeneracyValues
open OrdinaryBarFreeResolutionMixedFaces

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

include degeneracyLaw in
lemma boundary_degeneracy_facet (j : Fin (n + 2)) (k : Fin (n + 3)) :
    (degeneracyFunctor D (n + 1) j ⋙
      OrdinaryBarFreeResolutionBoundary.boundary hcof hfib D n P F G faceLaw) ⋙
        OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι k) =
    (diagram hcof hfib D n P F j ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ (SSet.boundary (n + 2)).ι)) ⋙
        OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι k) := by
  rw [CategoryTheory.Functor.assoc, OrdinaryBarFreeResolutionBoundary.boundary_face,
    CategoryTheory.Functor.assoc, ← OrdinaryBarChoiceCategory.reindex_comp,
    ← whiskerLeft_comp, SSet.boundary.ι_ι]
  simpa only [OrdinaryBarFreeResolutionBoundary.face, rawFace, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.delta_eq, Fin.rev_rev] using
    facet_equation hcof hfib D n P F G faceLaw degeneracyLaw j k.rev

include degeneracyLaw in
lemma boundary_degeneracy (j : Fin (n + 2)) :
    degeneracyFunctor D (n + 1) j ⋙
      OrdinaryBarFreeResolutionBoundary.boundary hcof hfib D n P F G faceLaw =
    diagram hcof hfib D n P F j ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ (SSet.boundary (n + 2)).ι) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply OrdinaryBarChoiceBoundaryExt.hom_ext hcof hfib _ _
  intro k
  exact congr($(boundary_degeneracy_facet hcof hfib D n P F G faceLaw degeneracyLaw j k).map f)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegenerateBoundary
