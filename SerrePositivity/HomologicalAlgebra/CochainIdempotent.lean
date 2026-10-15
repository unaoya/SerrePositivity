module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # Images of idempotent chain maps

The equalizer of the identity and an idempotent gives its image, together with
canonical inclusion and projection maps. Equivariant chain maps induce maps on images.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]

/-- An idempotent endomorphism of a cochain complex. -/
structure CochainIdempotent (K : CochainComplex (ModuleCat.{u} R) ℤ) where
  map : K ⟶ K
  idem : map ≫ map = map

namespace CochainIdempotent
variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ}

/-- The image of an idempotent chain map. -/
abbrev image (e : CochainIdempotent K) := equalizer (𝟙 K) e.map

/-- The image embeds in the original complex. -/
abbrev inclusion (e : CochainIdempotent K) : e.image ⟶ K := equalizer.ι (𝟙 K) e.map

/-- The idempotent, regarded as a map onto its image. -/
def projection (e : CochainIdempotent K) : K ⟶ e.image :=
  equalizer.lift e.map (by rw [comp_id, e.idem])

@[simp, reassoc]
lemma projection_inclusion (e : CochainIdempotent K) :
    e.projection ≫ e.inclusion = e.map := equalizer.lift_ι _ _

@[simp, reassoc]
lemma inclusion_map (e : CochainIdempotent K) :
    e.inclusion ≫ e.map = e.inclusion := by
  simpa using (equalizer.condition (𝟙 K) e.map).symm

@[simp, reassoc]
lemma inclusion_projection (e : CochainIdempotent K) :
    e.inclusion ≫ e.projection = 𝟙 e.image := by
  apply (cancel_mono e.inclusion).1
  simp only [Category.assoc, projection_inclusion, inclusion_map, id_comp]

/-- A chain map commuting with two idempotents restricts to their images. -/
def imageMap (e : CochainIdempotent K) (d : CochainIdempotent L) (f : K ⟶ L)
    (hf : e.map ≫ f = f ≫ d.map) : e.image ⟶ d.image :=
  equalizer.lift (e.inclusion ≫ f) (by
    rw [comp_id, Category.assoc, ← hf, ← Category.assoc, inclusion_map])

@[simp, reassoc]
lemma imageMap_inclusion (e : CochainIdempotent K) (d : CochainIdempotent L)
    (f : K ⟶ L) (hf : e.map ≫ f = f ≫ d.map) :
    imageMap e d f hf ≫ d.inclusion = e.inclusion ≫ f := equalizer.lift_ι _ _

@[reassoc]
lemma projection_imageMap (e : CochainIdempotent K) (d : CochainIdempotent L)
    (f : K ⟶ L) (hf : e.map ≫ f = f ≫ d.map) :
    e.projection ≫ imageMap e d f hf = f ≫ d.projection := by
  apply (cancel_mono d.inclusion).1
  simp only [Category.assoc, imageMap_inclusion, projection_inclusion_assoc,
    projection_inclusion, hf]

@[simp]
lemma imageMap_id (e : CochainIdempotent K) :
    imageMap e e (𝟙 K) (by simp) = 𝟙 e.image := by
  apply (cancel_mono e.inclusion).1
  simp

lemma imageMap_comp (e : CochainIdempotent K) (d : CochainIdempotent L)
    (c : CochainIdempotent M) (f : K ⟶ L) (g : L ⟶ M)
    (hf : e.map ≫ f = f ≫ d.map) (hg : d.map ≫ g = g ≫ c.map) :
    imageMap e c (f ≫ g) (by rw [← Category.assoc, hf, Category.assoc, hg,
      Category.assoc]) = imageMap e d f hf ≫ imageMap d c g hg := by
  apply (cancel_mono c.inclusion).1
  simp only [Category.assoc, imageMap_inclusion, imageMap_inclusion_assoc]

end CochainIdempotent
end SerrePositivity
