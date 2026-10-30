module

public import SerrePositivity.KTheory.Adams.TensorCubeEigenspaces
public import SerrePositivity.PerfectComplex.CubicActionTensor
public import SerrePositivity.PerfectComplex.TensorHomotopy
public import SerrePositivity.HomologicalAlgebra.CochainTensorShuffle
public import SerrePositivity.HomologicalAlgebra.CochainTensorHomogeneous
public import SerrePositivity.HomologicalAlgebra.CochainTensorTriple
public import SerrePositivity.HomologicalAlgebra.CochainTensorSixShuffle
public import SerrePositivity.HomologicalAlgebra.CochainTensorSixHomogeneous
public import SerrePositivity.HomologicalAlgebra.CochainTensorSixRotation
public import SerrePositivity.HomologicalAlgebra.CochainTensorSixShuffleEquivariance

/-! # Separating a tensor cube into the cubes of its factors -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits
namespace Adams
variable {R : Type u} [CommRing R]

/-- Group the P factors and the Q factors in the cube of their tensor product. -/
def tensorCubeTensorIso (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    tensorCube (cochainTensor P Q) ≅ cochainTensor (tensorCube P) (tensorCube Q) :=
  cochainTensorSixShuffle P Q P Q P Q

@[reassoc]
lemma tensorCubeTensorIso_rotation (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    tensorCubeRotation (cochainTensor P Q) ≫ (tensorCubeTensorIso P Q).hom =
      (tensorCubeTensorIso P Q).hom ≫
        cochainTensorMap (tensorCubeRotation P) (tensorCubeRotation Q) :=
  cochainTensorSixShuffle_rotation P Q P Q P Q

end Adams
end SerrePositivity
