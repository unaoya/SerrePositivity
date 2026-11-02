module

public import SerrePositivity.PerfectComplex.Tensor.Perfect
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Shuffle
public import SerrePositivity.KTheory.Adams.TensorPower.TensorSquare
public import SerrePositivity.PerfectComplex.Eigen.Cubic
public import SerrePositivity.PerfectComplex.Eigen.Idempotent
public import Mathlib.Algebra.Homology.QuasiIso
public import SerrePositivity.HomologicalAlgebra.Complex.Idempotent
public import SerrePositivity.PerfectComplex.ClosedSupport.Cup
public import SerrePositivity.HomologicalAlgebra.CochainTensor.BaseChange
public import SerrePositivity.PerfectComplex.Eigen.CubicTensor

/-! # テンソル三乗の符号付き巡回作用と固有空間

## 概要

テンソル三乗の符号付きの巡回作用と三つの固有空間の複体を定め、指標の写像が擬同型を保つこと、基底変更が三次の作用と指標の像に絡むこと、テンソル三乗を因子の三乗に分けることを与える。

## 方針

固有空間は PerfectComplex/Eigen/Cubic の指標の射影で取る。

## 規約

`tensorCube*` の名前は群の外から参照されるので残す。

## 使われ方

`TensorPower/TensorCubeFiltration` 以下、`Adams/CyclicThree`。
-/

@[expose] public noncomputable section

universe u

section TensorCubePart

set_option backward.isDefEq.respectTransparency false
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

end TensorCubePart

section TensorCubeEigenspacesPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
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

end TensorCubeEigenspacesPart

section TensorCubeMapsPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits
namespace Adams
variable {R : Type u} [CommRing R]
variable {P Q : CochainComplex (ModuleCat.{u} R) ℤ}

lemma tensorCubeMap_quasiIso (f : P ⟶ Q) [QuasiIso f]
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q) :
    QuasiIso (tensorCubeMap f) := by
  have : QuasiIso (tensorSquareMap f) := cochainTensorMap_quasiIso hp hq hp hq f f
  exact cochainTensorMap_quasiIso (tensorSquare_perfect P hp) (tensorSquare_perfect Q hq)
    hp hq (tensorSquareMap f) f

variable [Invertible (3 : R)] (t : R) (ht : t ^ 2 + t + 1 = 0)

lemma tensorCubeEigenspaceMap_quasiIso (f : P ⟶ Q) [QuasiIso f]
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q) (j : Fin 3) :
    QuasiIso (tensorCubeEigenspaceMap t ht f j) := by
  have := tensorCubeMap_quasiIso f hp hq
  exact CochainIdempotent.imageMap_quasiIso _ _ _ _

lemma tensorCubeEigenspaceMap_homotopyEquivalence (f : P ⟶ Q) [QuasiIso f]
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q) (j : Fin 3) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (.up ℤ)
      (tensorCubeEigenspaceMap t ht f j) := by
  have := tensorCubeEigenspaceMap_quasiIso t ht f hp hq j
  exact (strictlyPerfectComplex_quasiIso_iff
    (tensorCubeEigenspace_perfect t ht P hp j)
    (tensorCubeEigenspace_perfect t ht Q hq j) _).mp inferInstance

end Adams
end SerrePositivity

end TensorCubeMapsPart

section TensorCubeBaseChangeEigenspacesPart

set_option backward.isDefEq.respectTransparency false
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

end TensorCubeBaseChangeEigenspacesPart

section TensorCubeTensorPart

set_option backward.isDefEq.respectTransparency false
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

end TensorCubeTensorPart
