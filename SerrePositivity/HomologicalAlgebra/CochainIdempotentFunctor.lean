module

public import SerrePositivity.HomologicalAlgebra.CochainIdempotent
public import SerrePositivity.HomologicalAlgebra.CochainIdempotentIso

/-! # Transport of split idempotent images through functors -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits
variable {R S : Type u} [CommRing R] [CommRing S]
namespace CochainIdempotent
variable {K : CochainComplex (ModuleCat.{u} R) ℤ}
variable (F : CochainComplex (ModuleCat.{u} R) ℤ ⥤
  CochainComplex (ModuleCat.{u} S) ℤ) (e : CochainIdempotent K)

/-- A functor transports the idempotence equation. -/
def mapFunctor : CochainIdempotent (F.obj K) where
  map := F.map e.map
  idem := by rw [← F.map_comp, e.idem]

/-- Split images are preserved without an assumption about general equalizers. -/
def imageFunctorIso : F.obj e.image ≅ (mapFunctor F e).image where
  hom := F.map e.inclusion ≫ (mapFunctor F e).projection
  inv := (mapFunctor F e).inclusion ≫ F.map e.projection
  hom_inv_id := by
    simp only [Category.assoc, projection_inclusion_assoc]
    change F.map e.inclusion ≫ F.map e.map ≫ F.map e.projection = _
    rw [← F.map_comp_assoc, inclusion_map, ← F.map_comp, inclusion_projection,
      F.map_id]
  inv_hom_id := by
    rw [Category.assoc, ← F.map_comp_assoc, projection_inclusion]
    change (mapFunctor F e).inclusion ≫ (mapFunctor F e).map ≫
      (mapFunctor F e).projection = _
    rw [inclusion_map_assoc, inclusion_projection]

@[reassoc]
lemma imageFunctorIso_hom_inclusion :
    (imageFunctorIso F e).hom ≫ (mapFunctor F e).inclusion = F.map e.inclusion := by
  change F.map e.inclusion ≫ (mapFunctor F e).projection ≫
    (mapFunctor F e).inclusion = _
  rw [projection_inclusion]
  change F.map e.inclusion ≫ F.map e.map = _
  rw [← F.map_comp, inclusion_map]

@[reassoc]
lemma map_projection_imageFunctorIso_hom :
    F.map e.projection ≫ (imageFunctorIso F e).hom = (mapFunctor F e).projection := by
  change F.map e.projection ≫ F.map e.inclusion ≫ (mapFunctor F e).projection = _
  rw [← F.map_comp_assoc, projection_inclusion]
  change (mapFunctor F e).map ≫ (mapFunctor F e).projection = _
  rw [← projection_inclusion, Category.assoc, inclusion_projection, comp_id]

/-- Equivariant maps remain equivariant after applying a functor. -/
lemma mapFunctor_equivariance {L : CochainComplex (ModuleCat.{u} R) ℤ}
    (d : CochainIdempotent L) (f : K ⟶ L) (hf : e.map ≫ f = f ≫ d.map) :
    (mapFunctor F e).map ≫ F.map f = F.map f ≫ (mapFunctor F d).map := by
  change F.map e.map ≫ F.map f = F.map f ≫ F.map d.map
  rw [← F.map_comp, hf, F.map_comp]

@[reassoc]
lemma imageFunctorIso_naturality {L : CochainComplex (ModuleCat.{u} R) ℤ}
    (d : CochainIdempotent L) (f : K ⟶ L) (hf : e.map ≫ f = f ≫ d.map) :
    F.map (imageMap e d f hf) ≫ (imageFunctorIso F d).hom =
      (imageFunctorIso F e).hom ≫
        imageMap (mapFunctor F e) (mapFunctor F d) (F.map f)
          (mapFunctor_equivariance F e d f hf) := by
  apply (cancel_mono (mapFunctor F d).inclusion).mp
  simp only [Category.assoc, imageFunctorIso_hom_inclusion,
    imageMap_inclusion, imageFunctorIso_hom_inclusion_assoc]
  rw [← F.map_comp, imageMap_inclusion, F.map_comp]

/-- Compare the transported image with any projector having the same underlying map. -/
def imageFunctorIsoOfMapEq (d : CochainIdempotent (F.obj K)) (h : F.map e.map = d.map) :
    F.obj e.image ≅ d.image :=
  imageFunctorIso F e ≪≫ imageIso _ _ (Iso.refl _) (by
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    rw [comp_id, id_comp]
    exact h)

@[reassoc]
lemma imageFunctorIsoOfMapEq_hom_inclusion
    (d : CochainIdempotent (F.obj K)) (h : F.map e.map = d.map) :
    (imageFunctorIsoOfMapEq F e d h).hom ≫ d.inclusion = F.map e.inclusion := by
  simp only [imageFunctorIsoOfMapEq, Iso.trans_hom, Category.assoc,
    imageIso_hom_inclusion, Iso.refl_hom, comp_id, imageFunctorIso_hom_inclusion]

end CochainIdempotent
end SerrePositivity
