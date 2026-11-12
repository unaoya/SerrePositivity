module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryIntersection
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：標準境界は、同じホーンに欠けた標準面をその境界に沿って付加した pushout。
方針：部分複体の双カルテジアン四角形を、低次元の境界と標準面の同型で移す。
規約：四つの射を元の標準包含に固定する。
使われ方：境界全体の native Hom と分類先の厳密な同じ pullback 表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-- 同じホーン、欠けた面、その交わり、標準境界の双カルテジアン四角形。 -/
def hornBoundaryBicartSq (n : ℕ) (i : Fin (n + 2)) :
    Subcomplex.BicartSq
      (horn.{u} (n + 1) i ⊓ stdSimplex.face {i}ᶜ)
      (horn (n + 1) i) (stdSimplex.face {i}ᶜ) (boundary (n + 1)) where
  sup_eq := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.horn_sup_missingFace (n + 1) i
  inf_eq := rfl

/-- 同じホーンの元の標準境界への包含。 -/
def hornBoundaryInclusion (n : ℕ) (i : Fin (n + 2)) :
    (horn (n + 1) i : SSet.{u}) ⟶ boundary (n + 1) :=
  Subcomplex.homOfLE (hornBoundaryBicartSq n i).le₂₄

/-- 欠けた面の境界から同じホーンへの、元の標準面包含に沿う射。 -/
def hornMissingFaceBoundaryToHorn (n : ℕ) (i : Fin (n + 2)) :
    (boundary n : SSet.{u}) ⟶ horn (n + 1) i :=
  (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornMissingFaceBoundaryIso n i).hom ≫ Subcomplex.homOfLE inf_le_left

/-- 同じ共有境界のホーンへの射は、元の標準面の包含を保持する。 -/
lemma hornMissingFaceBoundaryToHorn_ι (n : ℕ) (i : Fin (n + 2)) :
    hornMissingFaceBoundaryToHorn.{u} n i ≫ (horn (n + 1) i).ι =
      (boundary n).ι ≫ stdSimplex.δ i := by
  rw [hornMissingFaceBoundaryToHorn, Category.assoc, Subcomplex.homOfLE_ι,
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornMissingFaceBoundaryIso_hom_ι]

/-- 元の標準境界を、ホーンと欠けた一面から同じ四つの包含で構成する pushout。 -/
lemma hornBoundaryAttachment_isPushout (n : ℕ) (i : Fin (n + 2)) :
    IsPushout (hornMissingFaceBoundaryToHorn.{u} n i) (boundary n).ι
      (hornBoundaryInclusion n i) (boundary.ι i) := by
  fapply (hornBoundaryBicartSq.{u} n i).isPushout.of_iso'
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornMissingFaceBoundaryIso n i) (Iso.refl _)
    (stdSimplex.faceSingletonComplIso i) (Iso.refl _)
  · simp only [hornMissingFaceBoundaryToHorn, Iso.refl_hom, Category.comp_id]
  · apply (cancel_mono (stdSimplex.face {i}ᶜ).ι).mp
    rw [Category.assoc, Subcomplex.homOfLE_ι, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornMissingFaceBoundaryIso_hom_ι,
      Category.assoc, stdSimplex.faceSingletonComplIso_hom_ι]
  · simp only [hornBoundaryInclusion, Iso.refl_hom, Category.id_comp, Category.comp_id]
  · apply (cancel_mono (boundary (n + 1)).ι).mp
    simp only [Category.assoc, Subcomplex.homOfLE_ι,
      stdSimplex.faceSingletonComplIso_hom_ι, Iso.refl_hom, Category.comp_id, boundary.ι_ι]

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
