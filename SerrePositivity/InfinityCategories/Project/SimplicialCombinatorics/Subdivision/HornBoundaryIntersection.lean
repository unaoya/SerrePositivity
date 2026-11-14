module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.HornBoundaryAttachment

/-!
概要：ホーンと欠けた面の交わりは、その面の標準境界と同型。
方針：標準面包含による境界の像を計算し、単射な像への射の同型を使う。
規約：同型は元の標準面包含を保持する。
使われ方：境界の貼合せに現れる共有部分を低次元の実際の境界へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-- 欠けた面の標準境界の像は、同じホーンと面の交わり。 -/
lemma boundary_missingFace_image (n : ℕ) (i : Fin (n + 2)) :
    (boundary.{u} n).image (stdSimplex.δ i) =
      horn (n + 1) i ⊓ stdSimplex.face {i}ᶜ := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.horn_missingFace_preimage n i, ← stdSimplex.range_δ i]
  ext m s
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, ⟨x, rfl⟩⟩
  · rintro ⟨h, x, rfl⟩
    exact ⟨x, h, rfl⟩

/-- 同じ共有部分と低次元の境界を、標準面包含で同定する。 -/
def hornMissingFaceBoundaryIso (n : ℕ) (i : Fin (n + 2)) :
    (boundary n : SSet.{u}) ≅
      (horn (n + 1) i ⊓ stdSimplex.face {i}ᶜ : (Δ[n + 1] : SSet.{u}).Subcomplex) := by
  let f := (boundary.{u} n).toImage (stdSimplex.δ i)
  haveI : Mono f := by
    apply mono_of_mono_fac ((boundary n).toImage_ι (stdSimplex.δ i))
  haveI : IsIso f := isIso_of_mono_of_epi f
  exact asIso f ≪≫ Subcomplex.eqToIso (boundary_missingFace_image n i)

/-- 部分複体の等式による同型は、元の包含を保持する。 -/
lemma subcomplex_eqToIso_hom_ι {X : SSet.{u}} {A B : X.Subcomplex} (h : A = B) :
    (Subcomplex.eqToIso h).hom ≫ B.ι = A.ι := by
  subst B
  rfl

/-- 同じ交わりの同型は、元の低次元の境界と標準面の包含を保持する。 -/
lemma hornMissingFaceBoundaryIso_hom_ι (n : ℕ) (i : Fin (n + 2)) :
    (hornMissingFaceBoundaryIso.{u} n i).hom ≫
      (horn (n + 1) i ⊓ stdSimplex.face {i}ᶜ).ι =
        (boundary n).ι ≫ stdSimplex.δ i := by
  dsimp only [hornMissingFaceBoundaryIso, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, subcomplex_eqToIso_hom_ι]
  exact (boundary n).toImage_ι (stdSimplex.δ i)

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
