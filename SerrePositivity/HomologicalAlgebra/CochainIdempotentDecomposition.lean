module

public import SerrePositivity.HomologicalAlgebra.CochainIdempotent
public import SerrePositivity.HomologicalAlgebra.CochainBiproduct

/-! # Finite orthogonal idempotent decompositions of complexes -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits Preadditive
variable {R : Type u} [CommRing R]

namespace CochainIdempotent
variable {K : CochainComplex (ModuleCat.{u} R) ℤ}

/-- Orthogonal idempotents have zero cross-component maps. -/
lemma inclusion_projection_eq_zero (e d : CochainIdempotent K)
    (h : e.map ≫ d.map = 0) : e.inclusion ≫ d.projection = 0 := by
  apply (cancel_mono d.inclusion).1
  rw [Category.assoc, projection_inclusion, zero_comp]
  rw [← e.inclusion_map, Category.assoc, h, comp_zero]

/-- The images of a finite orthogonal family summing to the identity decompose the complex. -/
def decompositionIso {J : Type} [Fintype J] (e : J → CochainIdempotent K)
    (horth : ∀ i j, i ≠ j → (e i).map ≫ (e j).map = 0)
    (hsum : ∑ j, (e j).map = 𝟙 K) : (⨁ fun j => (e j).image) ≅ K where
  hom := biproduct.desc fun j => (e j).inclusion
  inv := biproduct.lift fun j => (e j).projection
  hom_inv_id := by
    classical
    apply biproduct.hom_ext
    intro j
    apply biproduct.hom_ext'
    intro i
    by_cases h : i = j
    · subst j
      simp
    · simp only [Category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc,
        id_comp, biproduct.ι_π_ne _ h]
      exact inclusion_projection_eq_zero (e i) (e j) (horth i j h)
  inv_hom_id := by
    rw [biproduct.lift_desc]
    simpa only [projection_inclusion] using hsum

@[simp, reassoc]
lemma ι_decompositionIso_hom {J : Type} [Fintype J] (e : J → CochainIdempotent K)
    (horth : ∀ i j, i ≠ j → (e i).map ≫ (e j).map = 0)
    (hsum : ∑ j, (e j).map = 𝟙 K) (j : J) :
    biproduct.ι (fun j => (e j).image) j ≫ (decompositionIso e horth hsum).hom =
      (e j).inclusion := biproduct.ι_desc _ _

@[simp, reassoc]
lemma decompositionIso_inv_π {J : Type} [Fintype J] (e : J → CochainIdempotent K)
    (horth : ∀ i j, i ≠ j → (e i).map ≫ (e j).map = 0)
    (hsum : ∑ j, (e j).map = 𝟙 K) (j : J) :
    (decompositionIso e horth hsum).inv ≫ biproduct.π (fun j => (e j).image) j =
      (e j).projection := biproduct.lift_π _ _

/-- The complementary idempotent. -/
def complement (e : CochainIdempotent K) : CochainIdempotent K where
  map := 𝟙 K - e.map
  idem := Idempotents.idem_of_id_sub_idem e.map e.idem

@[simp]
lemma map_comp_complement (e : CochainIdempotent K) : e.map ≫ e.complement.map = 0 := by
  simp [complement, comp_sub, e.idem]

@[simp]
lemma complement_comp_map (e : CochainIdempotent K) : e.complement.map ≫ e.map = 0 := by
  simp [complement, sub_comp, e.idem]

@[simp]
lemma map_add_complement (e : CochainIdempotent K) : e.map + e.complement.map = 𝟙 K := by
  simp [complement]

/-- An idempotent and its complement split the original complex as a binary biproduct. -/
def complementIso (e : CochainIdempotent K) : e.image ⊞ e.complement.image ≅ K where
  hom := biprod.desc e.inclusion e.complement.inclusion
  inv := biprod.lift e.projection e.complement.projection
  hom_inv_id := by
    apply biprod.hom_ext
    · apply biprod.hom_ext'
      · simp
      · simp [inclusion_projection_eq_zero e.complement e (complement_comp_map e)]
    · apply biprod.hom_ext'
      · simp [inclusion_projection_eq_zero e e.complement (map_comp_complement e)]
      · simp
  inv_hom_id := by
    rw [biprod.lift_desc, projection_inclusion, projection_inclusion, map_add_complement]

end CochainIdempotent
end SerrePositivity
