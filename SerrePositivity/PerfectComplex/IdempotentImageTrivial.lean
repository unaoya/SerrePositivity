module

public import SerrePositivity.PerfectComplex.IdempotentImagePerfect

/-! # Images and supported classes of trivial idempotents

The zero and identity cases are shared by involution eigenspaces and cubic character images.
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]
variable {K : CochainComplex (ModuleCat.{u} R) ℤ}

/-- A zero complex has zero class for any closed support containing its homology. -/
lemma K0WithSupport.mk_eq_zero_of_isZero (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) (hz : IsZero K) :
    K0WithSupport.mk Z (supportedPerfectOnObj Z K hp hs) = 0 := by
  have hobj : IsZero (supportedPerfectOnObj Z K hp hs) :=
    IsZero.of_full_of_faithful_of_isZero
      (supportedPerfectOnInclusion Z ⋙ perfectHomotopyInclusion R) _
      ((homotopyQuot R).map_isZero hz)
  exact TriangulatedK0.mk_of_isZero _ hobj

namespace CochainIdempotent

/-- The image of the identity projector is canonically the original complex. -/
def imageIsoOfMapEqId (e : CochainIdempotent K) (he : e.map = 𝟙 K) : e.image ≅ K where
  hom := e.inclusion
  inv := e.projection
  hom_inv_id := e.inclusion_projection
  inv_hom_id := e.projection_inclusion.trans he

@[simp]
lemma imageIsoOfMapEqId_hom (e : CochainIdempotent K) (he : e.map = 𝟙 K) :
    (e.imageIsoOfMapEqId he).hom = e.inclusion := rfl

@[simp]
lemma imageIsoOfMapEqId_inv (e : CochainIdempotent K) (he : e.map = 𝟙 K) :
    (e.imageIsoOfMapEqId he).inv = e.projection := rfl

/-- The image of the zero projector is a zero complex. -/
lemma image_isZero_of_map_eq_zero (e : CochainIdempotent K) (he : e.map = 0) :
    IsZero e.image := by
  have hi : e.inclusion = 0 := by
    rw [← e.inclusion_map, he, comp_zero]
  rw [IsZero.iff_id_eq_zero, ← e.inclusion_projection, hi, zero_comp]

end CochainIdempotent
end SerrePositivity
