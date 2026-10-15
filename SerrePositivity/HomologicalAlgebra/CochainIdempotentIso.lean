module

public import SerrePositivity.HomologicalAlgebra.CochainIdempotent

/-! # Equivariant chain isomorphisms induce isomorphisms of idempotent images -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]
namespace CochainIdempotent
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

lemma equivariance_inv (e : CochainIdempotent K) (d : CochainIdempotent L)
    (f : K ≅ L) (h : e.map ≫ f.hom = f.hom ≫ d.map) :
    d.map ≫ f.inv = f.inv ≫ e.map := by
  have hz : f.inv ≫ e.map ≫ f.hom = d.map := by
    rw [h, Iso.inv_hom_id_assoc]
  exact (Iso.comp_inv_eq f).mpr (by simpa only [Category.assoc] using hz.symm)

def imageIso (e : CochainIdempotent K) (d : CochainIdempotent L)
    (f : K ≅ L) (h : e.map ≫ f.hom = f.hom ≫ d.map) : e.image ≅ d.image where
  hom := imageMap e d f.hom h
  inv := imageMap d e f.inv (equivariance_inv e d f h)
  hom_inv_id := by
    apply (cancel_mono e.inclusion).mp
    simp [Category.assoc, imageMap_inclusion, imageMap_inclusion_assoc]
  inv_hom_id := by
    apply (cancel_mono d.inclusion).mp
    simp [Category.assoc, imageMap_inclusion, imageMap_inclusion_assoc]

@[reassoc]
lemma imageIso_hom_inclusion (e : CochainIdempotent K) (d : CochainIdempotent L)
    (f : K ≅ L) (h : e.map ≫ f.hom = f.hom ≫ d.map) :
    (imageIso e d f h).hom ≫ d.inclusion = e.inclusion ≫ f.hom :=
  imageMap_inclusion e d f.hom h

end CochainIdempotent
end SerrePositivity
