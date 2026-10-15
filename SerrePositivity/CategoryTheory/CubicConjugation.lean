module
public import Mathlib.CategoryTheory.Iso

/-! # Conjugation of cubic endomorphisms and compatible projections -/
@[expose] public section
namespace SerrePositivity
open CategoryTheory Category

lemma conjugate_cube {C : Type*} [Category C] {Q L : C}
    (e : Q ≅ L) (t : L ⟶ L) (ht : t ≫ t ≫ t = 𝟙 L) :
    (e.hom ≫ t ≫ e.inv) ≫ (e.hom ≫ t ≫ e.inv) ≫ (e.hom ≫ t ≫ e.inv) = 𝟙 Q := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc, id_comp, Iso.hom_inv_id] using e.hom ≫= (ht =≫ e.inv)

lemma conjugate_projection {C : Type*} [Category C] {K Q L : C}
    (p : K ⟶ Q) (e : Q ≅ L) (g : K ⟶ L) (s : K ⟶ K) (t : L ⟶ L)
    (he : p ≫ e.hom = g) (hg : s ≫ g = g ≫ t) :
    p ≫ (e.hom ≫ t ≫ e.inv) = s ≫ p := by
  apply (cancel_mono e.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, comp_id]
  rw [← Category.assoc p e.hom, he, hg]

end SerrePositivity
