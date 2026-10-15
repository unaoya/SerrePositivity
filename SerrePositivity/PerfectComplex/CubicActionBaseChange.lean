module

public import SerrePositivity.PerfectComplex.CubicActionDecomposition
public import SerrePositivity.PerfectComplex.IdempotentImageFunctor
public import SerrePositivity.PerfectComplex.IdempotentImageIso
public import SerrePositivity.HomologicalAlgebra.BaseChange

/-! # Base change of cubic actions and their split character images -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits
variable {R S : Type u} [CommRing R] [CommRing S]
namespace CochainCubicAction
variable (φ : R →+* S) {K : CochainComplex (ModuleCat.{u} R) ℤ}

/-- Transport the cubic equation through extension of scalars. -/
def baseChange (τ : CochainCubicAction K) :
    CochainCubicAction (SerrePositivity.baseChange φ K) where
  map := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map τ.map
  cube := by rw [← Functor.map_comp, ← Functor.map_comp, τ.cube, CategoryTheory.Functor.map_id]

variable [Invertible (3 : R)] [Invertible (3 : S)]

lemma map_invOf_three : φ (⅟(3 : R)) = ⅟(3 : S) := by
  let : Invertible (φ (3 : R)) := by rw [map_ofNat]; infer_instance
  simpa only [map_ofNat] using map_invOf φ (3 : R)

lemma baseChange_projectorMap (τ : CochainCubicAction K) (a : R) :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map (τ.projectorMap a) =
      (baseChange φ τ).projectorMap (φ a) := by
  simp only [projectorMap, extendScalars_mapHomologicalComplex_smul,
    map_invOf_three, Functor.map_add, CategoryTheory.Functor.map_id, Functor.map_comp, map_pow]
  rfl

/-- The image of a split character projector commutes with base change. -/
def characterBaseChangeIso (τ : CochainCubicAction K) (t : R) (ht : t ^ 3 = 1)
    (j : Fin 3) :
    SerrePositivity.baseChange φ (τ.characterProjector t ht j).image ≅
      ((baseChange φ τ).characterProjector (φ t)
        (by rw [← map_pow, ht, map_one]) j).image :=
  CochainIdempotent.imageFunctorIsoOfMapEq
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)) (τ.characterProjector t ht j)
    ((baseChange φ τ).characterProjector (φ t) (by rw [← map_pow, ht, map_one]) j) (by
      simpa only [characterProjector, projector, cubicCharacter, map_pow] using
        baseChange_projectorMap φ τ (cubicCharacter t j))

@[reassoc]
lemma characterBaseChangeIso_hom_inclusion (τ : CochainCubicAction K)
    (t : R) (ht : t ^ 3 = 1) (j : Fin 3) :
    (characterBaseChangeIso φ τ t ht j).hom ≫
      ((baseChange φ τ).characterProjector (φ t)
        (by rw [← map_pow, ht, map_one]) j).inclusion =
      ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
        (τ.characterProjector t ht j).inclusion := by
  simp only [characterBaseChangeIso, CochainIdempotent.imageFunctorIsoOfMapEq_hom_inclusion]

end CochainCubicAction
end SerrePositivity
