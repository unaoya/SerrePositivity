module

public import SerrePositivity.PerfectComplex.Tensor.Perfect
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Shuffle
public import SerrePositivity.KTheory.Adams.TensorSquare

/-! # The signed cyclic action on tensor cubes -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category
open scoped TensorProduct
namespace Adams
variable {R : Type u} [CommRing R]

abbrev tensorCube (P : CochainComplex (ModuleCat.{u} R) ℤ) :=
  cochainTensor (cochainTensor P P) P

abbrev tensorCubeMap {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) :=
  cochainTensorTripleMap f f f

/-- The right cyclic permutation with the Koszul signs. -/
abbrev tensorCubeRotation (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    tensorCube P ⟶ tensorCube P := (cochainTensorRotationIso P P P).hom

lemma tensorCubeRotation_cube (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    tensorCubeRotation P ≫ tensorCubeRotation P ≫ tensorCubeRotation P = 𝟙 _ :=
  cochainTensorRotation_cube P P P

@[reassoc]
lemma tensorCubeRotation_naturality {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) :
    tensorCubeMap f ≫ tensorCubeRotation Q = tensorCubeRotation P ≫ tensorCubeMap f :=
  cochainTensorRotation_naturality f f f

@[simp]
lemma tensorCubeMap_id (P : CochainComplex (ModuleCat.{u} R) ℤ) : tensorCubeMap (𝟙 P) = 𝟙 _ := by
  simp only [tensorCubeMap, cochainTensorTripleMap, cochainTensorMap_id]

lemma tensorCubeMap_comp {P Q T : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (g : Q ⟶ T) : tensorCubeMap (f ≫ g) = tensorCubeMap f ≫ tensorCubeMap g := by
  simp only [tensorCubeMap, cochainTensorTripleMap, cochainTensorMap_comp]

lemma tensorCube_perfect (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) : strictlyPerfectComplex R (tensorCube P) :=
  strictlyPerfectComplex_cochainTensor _ P (tensorSquare_perfect P hp) hp

lemma tensorCube_support {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (hp : strictlyPerfectComplex R P)
    (hs : HasHomologySupportOn Z P) : HasHomologySupportOn Z (tensorCube P) :=
  (tensorSquare_support hp hs).cochainTensor_left (tensorSquare_perfect P hp) P

lemma tensorCubeRotation_apply_ι (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k n : ℤ) (h : i + j + k = n) (x : P.X i) (y : P.X j) (z : P.X k) :
    (tensorCubeRotation P).f n
      (cochainTensorTripleι P P P i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z)) =
      ((i + j) * k).negOnePow •
        (cochainTensorTripleι P P P k i j n (by omega) ((z ⊗ₜ[R] x) ⊗ₜ[R] y)) :=
  cochainTensorRotation_apply_ι P P P i j k n h x y z

end Adams
end SerrePositivity
