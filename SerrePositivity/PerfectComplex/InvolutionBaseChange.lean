module

public import SerrePositivity.PerfectComplex.IdempotentImageFunctor
public import SerrePositivity.PerfectComplex.IdempotentImageIso
public import SerrePositivity.PerfectComplex.InvolutionMaps
public import SerrePositivity.HomologicalAlgebra.BaseChange

/-! # Base change of involution eigenspaces -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits
variable {R S : Type u} [CommRing R] [CommRing S]
namespace CochainInvolution
variable (φ : R →+* S) {K : CochainComplex (ModuleCat.{u} R) ℤ}

def baseChange (t : CochainInvolution K) :
    CochainInvolution (SerrePositivity.baseChange φ K) where
  map := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map t.map
  sq := by rw [← Functor.map_comp, t.sq, CategoryTheory.Functor.map_id]

variable [Invertible (2 : R)] [Invertible (2 : S)]

lemma map_invOf_two : φ (⅟(2 : R)) = ⅟(2 : S) := by
  let : Invertible (φ (2 : R)) := by rw [map_ofNat]; infer_instance
  simpa only [map_ofNat] using map_invOf φ (2 : R)

lemma baseChange_positive_map (t : CochainInvolution K) :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map t.positive.map =
      (baseChange φ t).positive.map := by
  change ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
      ((⅟(2 : R)) • (𝟙 K + t.map)) = _
  rw [extendScalars_mapHomologicalComplex_smul, map_invOf_two,
    Functor.map_add, CategoryTheory.Functor.map_id]
  rfl

lemma baseChange_negative_map (t : CochainInvolution K) :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map t.negative.map =
      (baseChange φ t).negative.map := by
  change ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
      (𝟙 K - t.positive.map) = _
  rw [Functor.map_sub, CategoryTheory.Functor.map_id, baseChange_positive_map]
  rfl

def positiveBaseChangeIso (t : CochainInvolution K) :
    SerrePositivity.baseChange φ t.positive.image ≅ (baseChange φ t).positive.image :=
  CochainIdempotent.imageFunctorIsoOfMapEq
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)) t.positive
    (baseChange φ t).positive (baseChange_positive_map φ t)

def negativeBaseChangeIso (t : CochainInvolution K) :
    SerrePositivity.baseChange φ t.negative.image ≅ (baseChange φ t).negative.image :=
  CochainIdempotent.imageFunctorIsoOfMapEq
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)) t.negative
    (baseChange φ t).negative (baseChange_negative_map φ t)

@[reassoc]
lemma positiveBaseChangeIso_hom_inclusion (t : CochainInvolution K) :
    (positiveBaseChangeIso φ t).hom ≫ (baseChange φ t).positive.inclusion =
      ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map t.positive.inclusion := by
  simp only [positiveBaseChangeIso, CochainIdempotent.imageFunctorIsoOfMapEq_hom_inclusion]

@[reassoc]
lemma negativeBaseChangeIso_hom_inclusion (t : CochainInvolution K) :
    (negativeBaseChangeIso φ t).hom ≫ (baseChange φ t).negative.inclusion =
      ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map t.negative.inclusion := by
  simp only [negativeBaseChangeIso, CochainIdempotent.imageFunctorIsoOfMapEq_hom_inclusion]

end CochainInvolution
end SerrePositivity
