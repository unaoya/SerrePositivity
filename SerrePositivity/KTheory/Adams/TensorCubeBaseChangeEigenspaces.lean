module

public import SerrePositivity.PerfectComplex.Tensor.Perfect
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Shuffle
public import SerrePositivity.PerfectComplex.ClosedSupport.Cup
public import SerrePositivity.HomologicalAlgebra.CochainTensor.BaseChange
public import SerrePositivity.PerfectComplex.Eigen.Cubic
public import SerrePositivity.KTheory.Adams.TensorCubeEigenspaces

/-! # Base change intertwines the cubic action and its character images -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits
variable {R S : Type u} [CommRing R] [CommRing S]
namespace Adams

abbrev tensorCubeBaseChangeIso (φ : R →+* S)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    baseChange φ (tensorCube P) ≅ tensorCube (baseChange φ P) :=
  cochainTensorTripleBaseChangeIso φ P P P

@[reassoc]
lemma tensorCubeBaseChangeIso_rotation (φ : R →+* S)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
        (tensorCubeRotation P) ≫ (tensorCubeBaseChangeIso φ P).hom =
      (tensorCubeBaseChangeIso φ P).hom ≫ tensorCubeRotation (baseChange φ P) :=
  cochainTensorTripleBaseChangeIso_rotation φ P P P

variable [Invertible (3 : R)] [Invertible (3 : S)]

/-- Base change of each cubic character image, using the transported ambient root. -/
def tensorCubeCharacterBaseChangeIso (φ : R →+* S)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (t : R) (ht : t ^ 3 = 1) (j : Fin 3) :
    baseChange φ ((tensorCubeAction P).characterProjector t ht j).image ≅
      ((tensorCubeAction (baseChange φ P)).characterProjector (φ t)
        (by rw [← map_pow, ht, map_one]) j).image :=
  CochainCubicAction.characterBaseChangeIso φ (tensorCubeAction P) t ht j ≪≫
    CochainIdempotent.imageIso _ _ (tensorCubeBaseChangeIso φ P)
      (CochainCubicAction.projectorMap_naturality
        ((tensorCubeAction P).baseChange φ) (tensorCubeAction (baseChange φ P))
        (tensorCubeBaseChangeIso φ P).hom (tensorCubeBaseChangeIso_rotation φ P)
        (cubicCharacter (φ t) j))

end Adams
end SerrePositivity
