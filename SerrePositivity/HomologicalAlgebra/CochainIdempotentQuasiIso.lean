module

public import SerrePositivity.HomologicalAlgebra.CochainIdempotent
public import Mathlib.Algebra.Homology.QuasiIso

/-! # Quasi-isomorphisms on idempotent images -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]

namespace CochainIdempotent
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

/-- The restriction of an equivariant map is a retract of that map in the arrow category. -/
def imageMapRetract (e : CochainIdempotent K) (d : CochainIdempotent L)
    (f : K ⟶ L) (hf : e.map ≫ f = f ≫ d.map) :
    RetractArrow (imageMap e d f hf) f where
  i := Arrow.homMk e.inclusion d.inclusion (imageMap_inclusion e d f hf).symm
  r := Arrow.homMk e.projection d.projection (projection_imageMap e d f hf)
  retract := by
    apply Arrow.hom_ext <;> simp

/-- Equivariant quasi-isomorphisms restrict to quasi-isomorphisms of idempotent images. -/
lemma imageMap_quasiIso (e : CochainIdempotent K) (d : CochainIdempotent L)
    (f : K ⟶ L) (hf : e.map ≫ f = f ≫ d.map) [QuasiIso f] :
    QuasiIso (imageMap e d f hf) :=
  quasiIso_of_retractArrow (imageMapRetract e d f hf)

end CochainIdempotent
end SerrePositivity
