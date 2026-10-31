module

public import SerrePositivity.KTheory.Adams.TensorCube
public import SerrePositivity.PerfectComplex.Eigen.Cubic

/-! # The three eigenspace complexes of a signed tensor cube -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits
namespace Adams
variable {R : Type u} [CommRing R]

/-- The signed cyclic generator as a cubic chain action. -/
def tensorCubeAction (P : CochainComplex (ModuleCat.{u} R) ℤ) : CochainCubicAction (tensorCube P) :=
  ⟨tensorCubeRotation P, tensorCubeRotation_cube P⟩

variable [Invertible (3 : R)] (t : R) (ht : t ^ 2 + t + 1 = 0)

abbrev tensorCubeProjector (P : CochainComplex (ModuleCat.{u} R) ℤ) (j : Fin 3) :=
  (tensorCubeAction P).characterProjector t (cube_eq_one_of_cubic_relation t ht) j

abbrev tensorCubeEigenspace (P : CochainComplex (ModuleCat.{u} R) ℤ) (j : Fin 3) :=
  (tensorCubeProjector t ht P j).image

/-- The cube is the biproduct of its three character subcomplexes. -/
def tensorCubeDecompositionIso (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (⨁ fun j : Fin 3 => tensorCubeEigenspace t ht P j) ≅ tensorCube P :=
  (tensorCubeAction P).characterDecompositionIso t ht

lemma tensorCubeEigenspace_perfect (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (j : Fin 3) :
    strictlyPerfectComplex R (tensorCubeEigenspace t ht P j) :=
  (tensorCubeProjector t ht P j).image_strictlyPerfect (tensorCube_perfect P hp)

lemma tensorCubeEigenspace_support {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (hp : strictlyPerfectComplex R P)
    (hs : HasHomologySupportOn Z P) (j : Fin 3) :
    HasHomologySupportOn Z (tensorCubeEigenspace t ht P j) :=
  (tensorCubeProjector t ht P j).image_support (tensorCube_support hp hs)

@[reassoc]
lemma tensorCubeEigenspace_inclusion_rotation (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (j : Fin 3) :
    (tensorCubeProjector t ht P j).inclusion ≫ tensorCubeRotation P =
      cubicCharacter t j • (tensorCubeProjector t ht P j).inclusion :=
  (tensorCubeAction P).projector_inclusion_eigen _
    (cubicCharacter_cube t (cube_eq_one_of_cubic_relation t ht) j)

@[reassoc]
lemma tensorCubeProjector_naturality {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (j : Fin 3) :
    (tensorCubeProjector t ht P j).map ≫ tensorCubeMap f =
      tensorCubeMap f ≫ (tensorCubeProjector t ht Q j).map :=
  (tensorCubeAction P).projectorMap_naturality (tensorCubeAction Q) (tensorCubeMap f)
    (tensorCubeRotation_naturality f).symm (cubicCharacter t j)

/-- The induced chain map on one character part. -/
def tensorCubeEigenspaceMap {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (j : Fin 3) : tensorCubeEigenspace t ht P j ⟶ tensorCubeEigenspace t ht Q j :=
  (tensorCubeProjector t ht P j).imageMap (tensorCubeProjector t ht Q j) (tensorCubeMap f)
    (tensorCubeProjector_naturality t ht f j)

@[simp, reassoc]
lemma tensorCubeEigenspaceMap_inclusion {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (j : Fin 3) :
    tensorCubeEigenspaceMap t ht f j ≫ (tensorCubeProjector t ht Q j).inclusion =
      (tensorCubeProjector t ht P j).inclusion ≫ tensorCubeMap f :=
  CochainIdempotent.imageMap_inclusion _ _ _ _

@[simp]
lemma tensorCubeEigenspaceMap_id (P : CochainComplex (ModuleCat.{u} R) ℤ) (j : Fin 3) :
    tensorCubeEigenspaceMap t ht (𝟙 P) j = 𝟙 _ := by
  apply (cancel_mono (tensorCubeProjector t ht P j).inclusion).mp
  simp only [tensorCubeEigenspaceMap_inclusion, tensorCubeMap_id, comp_id, id_comp]

lemma tensorCubeEigenspaceMap_comp {P Q U : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (g : Q ⟶ U) (j : Fin 3) :
    tensorCubeEigenspaceMap t ht (f ≫ g) j =
      tensorCubeEigenspaceMap t ht f j ≫ tensorCubeEigenspaceMap t ht g j := by
  apply (cancel_mono (tensorCubeProjector t ht U j).inclusion).mp
  simp only [Category.assoc, tensorCubeEigenspaceMap_inclusion,
    tensorCubeEigenspaceMap_inclusion_assoc, tensorCubeMap_comp]

end Adams
end SerrePositivity
