module

public import SerrePositivity.HomologicalAlgebra.Complex.Idempotent
public import SerrePositivity.HomologicalAlgebra.CochainTensorHomotopy

/-! # Tensor products of idempotent images -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R]
namespace CochainIdempotent
variable {P Q : CochainComplex (ModuleCat.{u} R) ℤ}

def tensor (e : CochainIdempotent P) (d : CochainIdempotent Q) :
    CochainIdempotent (cochainTensor P Q) where
  map := cochainTensorMap e.map d.map
  idem := by rw [cochainTensorMap_comp, e.idem, d.idem]

@[reassoc]
lemma tensor_inclusions_map (e : CochainIdempotent P) (d : CochainIdempotent Q) :
    cochainTensorMap e.inclusion d.inclusion ≫ (tensor e d).map =
      cochainTensorMap e.inclusion d.inclusion := by
  change cochainTensorMap e.inclusion d.inclusion ≫ cochainTensorMap e.map d.map = _
  rw [cochainTensorMap_comp, inclusion_map, inclusion_map]

def imageTensorIso (e : CochainIdempotent P) (d : CochainIdempotent Q) :
    cochainTensor e.image d.image ≅ (tensor e d).image where
  hom := cochainTensorMap e.inclusion d.inclusion ≫ (tensor e d).projection
  inv := (tensor e d).inclusion ≫ cochainTensorMap e.projection d.projection
  hom_inv_id := by
    change cochainTensorMap e.inclusion d.inclusion ≫ (tensor e d).projection ≫
      (tensor e d).inclusion ≫ cochainTensorMap e.projection d.projection = _
    rw [projection_inclusion_assoc, tensor_inclusions_map_assoc, cochainTensorMap_comp,
      inclusion_projection, inclusion_projection, cochainTensorMap_id]
  inv_hom_id := by
    change (tensor e d).inclusion ≫
      (cochainTensorMap e.projection d.projection ≫ cochainTensorMap e.inclusion d.inclusion) ≫
      (tensor e d).projection = _
    rw [cochainTensorMap_comp, projection_inclusion, projection_inclusion]
    change (tensor e d).inclusion ≫ (tensor e d).map ≫ (tensor e d).projection = _
    rw [← Category.assoc, inclusion_map, inclusion_projection]

@[reassoc]
lemma imageTensorIso_hom_inclusion (e : CochainIdempotent P) (d : CochainIdempotent Q) :
    (imageTensorIso e d).hom ≫ (tensor e d).inclusion =
      cochainTensorMap e.inclusion d.inclusion := by
  change (cochainTensorMap e.inclusion d.inclusion ≫ (tensor e d).projection) ≫
    (tensor e d).inclusion = _
  rw [Category.assoc, projection_inclusion, tensor_inclusions_map]

end CochainIdempotent
end SerrePositivity
