module

public import SerrePositivity.HomologicalAlgebra.CochainIdempotentSum

/-! # Finite sums of orthogonal idempotent images -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits Preadditive
variable {R : Type u} [CommRing R]
namespace CochainIdempotent
variable {K : CochainComplex (ModuleCat.{u} R) ℤ}
variable {J : Type} [Fintype J] (e : J → CochainIdempotent K) (d : CochainIdempotent K)
variable (horth : ∀ i j, i ≠ j → (e i).map ≫ (e j).map = 0)
variable (hsum : ∑ j, (e j).map = d.map)

include horth hsum in
lemma map_comp_finiteSum (j : J) : (e j).map ≫ d.map = (e j).map := by
  classical
  rw [← hsum, comp_sum]
  rw [Finset.sum_eq_single j]
  · exact (e j).idem
  · intro b _ hb
    exact horth j b (Ne.symm hb)
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

include horth hsum in
@[reassoc]
lemma inclusion_finiteSum_map (j : J) : (e j).inclusion ≫ d.map = (e j).inclusion := by
  rw [← (e j).inclusion_map, Category.assoc, map_comp_finiteSum e d horth hsum]

/-- The images of orthogonal idempotents summing to d decompose the image of d. -/
def imageFiniteSumIso : (⨁ fun j => (e j).image) ≅ d.image where
  hom := biproduct.desc (fun j => (e j).inclusion) ≫ d.projection
  inv := d.inclusion ≫ biproduct.lift (fun j => (e j).projection)
  hom_inv_id := by
    classical
    apply biproduct.hom_ext
    intro j
    apply biproduct.hom_ext'
    intro i
    by_cases h : i = j
    · subst j
      simp [Category.assoc, projection_inclusion_assoc d,
        inclusion_finiteSum_map_assoc e d horth hsum]
    · simp only [Category.assoc, projection_inclusion_assoc, biproduct.lift_π,
        biproduct.ι_desc_assoc, inclusion_finiteSum_map_assoc e d horth hsum,
        id_comp, biproduct.ι_π_ne _ h]
      exact inclusion_projection_eq_zero (e i) (e j) (horth i j h)
  inv_hom_id := by
    change d.inclusion ≫
      (biproduct.lift (fun j => (e j).projection) ≫
        biproduct.desc (fun j => (e j).inclusion)) ≫ d.projection = 𝟙 _
    rw [biproduct.lift_desc]
    simp only [projection_inclusion]
    rw [hsum, ← Category.assoc, inclusion_map, inclusion_projection]

@[reassoc]
lemma imageFiniteSumIso_hom_inclusion :
    (imageFiniteSumIso e d horth hsum).hom ≫ d.inclusion =
      biproduct.desc (fun j => (e j).inclusion) := by
  rw [imageFiniteSumIso, Category.assoc, projection_inclusion]
  apply biproduct.hom_ext'
  intro j
  simp only [biproduct.ι_desc_assoc, biproduct.ι_desc]
  exact inclusion_finiteSum_map e d horth hsum j

end CochainIdempotent
end SerrePositivity
