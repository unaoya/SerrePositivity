module

public import SerrePositivity.HomologicalAlgebra.CochainIdempotentDecomposition

/-! # Binary sums of orthogonal idempotent images -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]
namespace CochainIdempotent
variable {K : CochainComplex (ModuleCat.{u} R) ℤ}

@[ext]
lemma ext {e d : CochainIdempotent K} (h : e.map = d.map) : e = d := by
  cases e
  cases d
  cases h
  rfl

@[reassoc]
lemma image_eqToIso_inclusion {e d : CochainIdempotent K} (h : e = d) :
    (eqToIso (congrArg image h)).hom ≫ d.inclusion = e.inclusion := by
  cases h
  simp

def orthogonalSum (e d : CochainIdempotent K)
    (hed : e.map ≫ d.map = 0) (hde : d.map ≫ e.map = 0) : CochainIdempotent K where
  map := e.map + d.map
  idem := by simp [Preadditive.add_comp, Preadditive.comp_add, e.idem, d.idem, hed, hde]

@[reassoc]
lemma inclusion_orthogonalSum_map_left (e d : CochainIdempotent K)
    (hed : e.map ≫ d.map = 0) (hde : d.map ≫ e.map = 0) :
    e.inclusion ≫ (orthogonalSum e d hed hde).map = e.inclusion := by
  change e.inclusion ≫ (e.map + d.map) = _
  rw [Preadditive.comp_add, inclusion_map]
  have hz : e.inclusion ≫ d.map = 0 := by
    rw [← e.inclusion_map, Category.assoc, hed, comp_zero]
  rw [hz, add_zero]

@[reassoc]
lemma inclusion_orthogonalSum_map_right (e d : CochainIdempotent K)
    (hed : e.map ≫ d.map = 0) (hde : d.map ≫ e.map = 0) :
    d.inclusion ≫ (orthogonalSum e d hed hde).map = d.inclusion := by
  change d.inclusion ≫ (e.map + d.map) = _
  rw [Preadditive.comp_add, inclusion_map]
  have hz : d.inclusion ≫ e.map = 0 := by
    rw [← d.inclusion_map, Category.assoc, hde, comp_zero]
  rw [hz, zero_add]

def imageOrthogonalSumIso (e d : CochainIdempotent K)
    (hed : e.map ≫ d.map = 0) (hde : d.map ≫ e.map = 0) :
    e.image ⊞ d.image ≅ (orthogonalSum e d hed hde).image where
  hom := biprod.desc e.inclusion d.inclusion ≫ (orthogonalSum e d hed hde).projection
  inv := (orthogonalSum e d hed hde).inclusion ≫ biprod.lift e.projection d.projection
  hom_inv_id := by
    apply biprod.hom_ext
    · apply biprod.hom_ext'
      · simp [Category.assoc, projection_inclusion_assoc (orthogonalSum e d hed hde),
          inclusion_orthogonalSum_map_left_assoc e d hed hde]
      · simp [Category.assoc, projection_inclusion_assoc (orthogonalSum e d hed hde),
          inclusion_orthogonalSum_map_right_assoc e d hed hde,
          inclusion_projection_eq_zero d e hde]
    · apply biprod.hom_ext'
      · simp [Category.assoc, projection_inclusion_assoc (orthogonalSum e d hed hde),
          inclusion_orthogonalSum_map_left_assoc e d hed hde,
          inclusion_projection_eq_zero e d hed]
      · simp [Category.assoc, projection_inclusion_assoc (orthogonalSum e d hed hde),
          inclusion_orthogonalSum_map_right_assoc e d hed hde]
  inv_hom_id := by
    change (orthogonalSum e d hed hde).inclusion ≫
      (biprod.lift e.projection d.projection ≫ biprod.desc e.inclusion d.inclusion) ≫
      (orthogonalSum e d hed hde).projection = _
    rw [biprod.lift_desc, projection_inclusion, projection_inclusion]
    change (orthogonalSum e d hed hde).inclusion ≫ (orthogonalSum e d hed hde).map ≫
      (orthogonalSum e d hed hde).projection = _
    rw [← Category.assoc, inclusion_map, inclusion_projection]

@[reassoc]
lemma imageOrthogonalSumIso_hom_inclusion (e d : CochainIdempotent K)
    (hed : e.map ≫ d.map = 0) (hde : d.map ≫ e.map = 0) :
    (imageOrthogonalSumIso e d hed hde).hom ≫ (orthogonalSum e d hed hde).inclusion =
      biprod.desc e.inclusion d.inclusion := by
  change (biprod.desc e.inclusion d.inclusion ≫ (orthogonalSum e d hed hde).projection) ≫
    (orthogonalSum e d hed hde).inclusion = _
  rw [Category.assoc, projection_inclusion]
  apply biprod.hom_ext'
  · simp [inclusion_orthogonalSum_map_left]
  · simp [inclusion_orthogonalSum_map_right]

end CochainIdempotent
end SerrePositivity
