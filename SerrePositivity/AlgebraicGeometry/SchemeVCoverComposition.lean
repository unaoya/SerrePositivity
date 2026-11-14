module

public import SerrePositivity.AlgebraicGeometry.SchemeVCover
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
概要：スキームの付値持ち上げは合成・細分・Cartesian な底変換で保たれる。
方針：同じ付値環拡大を合成し、実際の pullback の普遍性で持ち上げを作る。
規約：底変換に平坦性を仮定しない。
使われ方：Rydh 3.10 の細分の付値判定を元の射と各底変換へ渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X Y Z : Scheme.{u}}

/-- スキームの v 判定は合成で保たれる。 -/
theorem IsSchemeVCover.comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsSchemeVCover f) (hg : IsSchemeVCover g) : IsSchemeVCover (f ≫ g) := by
  intro V _ _ k
  obtain ⟨W, hW, hvalW, e, l, he, hl⟩ := hg V k
  letI : IsDomain W := hW
  letI : ValuationRing W := hvalW
  obtain ⟨T, hT, hvalT, d, m, hd, hm⟩ := hf W l
  refine ⟨T, hT, hvalT, d.comp e, m,
    RingHom.FaithfullyFlat.stableUnderComposition e d he hd, ?_⟩
  rw [← Category.assoc, hm, Category.assoc, hl, ← Category.assoc, ← Spec.map_comp]
  rfl

/-- v 被覆である細分から、元の射のスキームの付値判定を得る。 -/
theorem IsSchemeVCover.of_comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (h : IsSchemeVCover (f ≫ g)) : IsSchemeVCover g := by
  intro V _ _ k
  obtain ⟨W, hW, hval, e, l, he, hl⟩ := h V k
  exact ⟨W, hW, hval, e, l ≫ f, he, by simpa only [Category.assoc] using hl⟩

/-- スキームの付値判定は、実際の pullback による底変換で保たれる。 -/
theorem IsSchemeVCover.baseChange {X' Y' : Scheme.{u}}
    {a : X' ⟶ X} {b : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (H : IsPullback a b f g) (hf : IsSchemeVCover f) : IsSchemeVCover b := by
  intro V _ _ k
  obtain ⟨W, hW, hval, e, l, he, hl⟩ := hf V (k ≫ g)
  have h : l ≫ f = (Spec.map (CommRingCat.ofHom e) ≫ k) ≫ g := by
    simpa only [Category.assoc] using hl
  exact ⟨W, hW, hval, e, H.lift l (Spec.map (CommRingCat.ofHom e) ≫ k) h, he,
    H.lift_snd _ _ h⟩

end SerrePositivity.AlgebraicGeometry
