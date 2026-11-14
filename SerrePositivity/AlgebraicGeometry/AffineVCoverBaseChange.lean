module

public import SerrePositivity.AlgebraicGeometry.AffineVCover
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Algebra.Category.Ring.Colimits

/-!
概要：affine v 被覆は環の pushout、すなわち affine な基底変更で保たれる。
方針：付値環への持ち上げを同じ試験写像と合わせ、pushout の普遍性で延長する。
規約：基底変更の射に平坦性を仮定しない。
使われ方：G0 の普遍的な付値判定と、2g の細分の各底変換。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]

/-- 環の実際の pushout による affine v 被覆の底変換。 -/
theorem IsAffineVCover.baseChange
    {f : A →+* B} (α : A →+* C) (g : B →+* D) (β : C →+* D)
    (H : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom α)
      (CommRingCat.ofHom g) (CommRingCat.ofHom β))
    (hf : IsAffineVCover f) : IsAffineVCover β := by
  intro V _ _ k
  obtain ⟨W, hW, hval, e, l, he, hl⟩ := hf V (k.comp α)
  have h : CommRingCat.ofHom f ≫ CommRingCat.ofHom l =
      CommRingCat.ofHom α ≫ CommRingCat.ofHom (e.comp k) := by
    apply CommRingCat.hom_ext
    exact hl
  let m := H.desc (CommRingCat.ofHom l) (CommRingCat.ofHom (e.comp k)) h
  refine ⟨W, hW, hval, e, m.hom, he, ?_⟩
  exact congrArg (fun q ↦ q.hom) (H.inr_desc _ _ h)

end SerrePositivity.AlgebraicGeometry
