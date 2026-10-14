module

public import SerrePositivity.PerfectComplex.InvolutionMaps

/-! # Anticommuting involutions exchange positive and negative eigenspaces -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits Preadditive
variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace CochainInvolution
variable {K : CochainComplex (ModuleCat.{u} R) ℤ}

lemma positive_negative_comm (t : CochainInvolution K) (a : K ⟶ K)
    (ha : t.map ≫ a = -(a ≫ t.map)) : t.positive.map ≫ a = a ≫ t.negative.map := by
  rw [t.negative_map]
  change ((⅟(2 : R)) • (𝟙 K + t.map)) ≫ a = a ≫ ((⅟(2 : R)) • (𝟙 K - t.map))
  rw [Linear.smul_comp, Linear.comp_smul, add_comp, comp_sub, id_comp, comp_id, ha]
  rw [sub_eq_add_neg]

lemma negative_positive_comm (t : CochainInvolution K) (a : K ⟶ K)
    (ha : t.map ≫ a = -(a ≫ t.map)) : t.negative.map ≫ a = a ≫ t.positive.map := by
  have h := positive_negative_comm t a ha
  change t.positive.map ≫ a = a ≫ (𝟙 K - t.positive.map) at h
  change (𝟙 K - t.positive.map) ≫ a = a ≫ t.positive.map
  rw [comp_sub, comp_id] at h
  rw [sub_comp, id_comp, h]
  abel

/-- An anticommuting chain involution gives a canonical isomorphism of the two eigenspaces. -/
def positiveNegativeIso (t : CochainInvolution K) (a : K ⟶ K)
    (ha : t.map ≫ a = -(a ≫ t.map)) (haa : a ≫ a = 𝟙 K) :
    t.positive.image ≅ t.negative.image where
  hom := CochainIdempotent.imageMap t.positive t.negative a (positive_negative_comm t a ha)
  inv := CochainIdempotent.imageMap t.negative t.positive a (negative_positive_comm t a ha)
  hom_inv_id := by
    apply (cancel_mono t.positive.inclusion).1
    simp only [Category.assoc, CochainIdempotent.imageMap_inclusion,
      CochainIdempotent.imageMap_inclusion_assoc, haa, comp_id, id_comp]
  inv_hom_id := by
    apply (cancel_mono t.negative.inclusion).1
    simp only [Category.assoc, CochainIdempotent.imageMap_inclusion,
      CochainIdempotent.imageMap_inclusion_assoc, haa, comp_id, id_comp]

end CochainInvolution
end SerrePositivity
