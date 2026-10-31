module

public import SerrePositivity.PerfectComplex.Eigen.Cubic
public import SerrePositivity.PerfectComplex.BiproductPerfect
public import SerrePositivity.PerfectComplex.Tensor.Perfect
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Shuffle
public import SerrePositivity.PerfectComplex.ClosedSupport.Functoriality
public import SerrePositivity.HomologicalAlgebra.Complex.Idempotent
public import SerrePositivity.PerfectComplex.Eigen.CubicClass

/-! # 三重テンソルの巡回和

## 概要

複体の三つのコピーへの標準的な巡回作用と、三つのテンソルの回転の巡回置換、巡回和の各和因子の完全性と台、巡回軌道の固有空間、巡回軌道の重み付き類の打ち消しを与える。

## 方針

三因子の回転（CochainTensor/Shuffle）を作用として使い、固有空間は `Eigen/Cubic` の射影で取る。

## 規約

PC3 の Cubic の作用と一体で動かす案もある（refactor-plan §4.3.1）。

## 使われ方

KTheory/Adams の三乗の Adams 作用素。
-/

@[expose] public noncomputable section

universe u v

section CochainCyclicThreePart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits Preadditive
variable {R : Type u} [CommRing R]
variable (U : CochainComplex (ModuleCat.{u} R) ℤ)

abbrev cochainCyclicThree := U ⊞ (U ⊞ U)

/-- Right cyclic permutation of three copies. -/
def cochainCyclicThreeRotation : cochainCyclicThree U ⟶ cochainCyclicThree U :=
  biprod.lift (biprod.snd ≫ biprod.snd) (biprod.lift biprod.fst (biprod.snd ≫ biprod.fst))

lemma cochainCyclicThreeRotation_cube :
    cochainCyclicThreeRotation U ≫ cochainCyclicThreeRotation U ≫
      cochainCyclicThreeRotation U = 𝟙 _ := by
  apply biprod.hom_ext
  · simp [cochainCyclicThreeRotation, Category.assoc]
  · apply biprod.hom_ext
    · simp [cochainCyclicThreeRotation, Category.assoc]
    · simp [cochainCyclicThreeRotation, Category.assoc]

def cochainCyclicThreeAction : CochainCubicAction (cochainCyclicThree U) :=
  ⟨cochainCyclicThreeRotation U, cochainCyclicThreeRotation_cube U⟩

/-- The eigenvector with first coordinate x has remaining coordinates a²x and ax. -/
def cochainCyclicThreeVector (a : R) : U ⟶ cochainCyclicThree U :=
  biprod.lift (𝟙 U) (biprod.lift (a ^ 2 • 𝟙 U) (a • 𝟙 U))

lemma cochainCyclicThreeVector_first (a : R) :
    cochainCyclicThreeVector U a ≫ biprod.fst = 𝟙 U := by
  simp only [cochainCyclicThreeVector, biprod.lift_fst]

lemma cochainCyclicThreeVector_eigen (a : R) (ha : a ^ 3 = 1) :
    cochainCyclicThreeVector U a ≫ cochainCyclicThreeRotation U =
      a • cochainCyclicThreeVector U a := by
  have hac : a * a ^ 2 = 1 := by rw [← pow_succ', ha]
  apply biprod.hom_ext
  · simp [cochainCyclicThreeVector, cochainCyclicThreeRotation, Category.assoc,
      Linear.smul_comp]
  · apply biprod.hom_ext
    · simp [cochainCyclicThreeVector, cochainCyclicThreeRotation, Category.assoc,
        Linear.smul_comp, smul_smul, hac]
    · simp [cochainCyclicThreeVector, cochainCyclicThreeRotation, Category.assoc,
        Linear.smul_comp, smul_smul, ← pow_two]

lemma cochainCyclicThreeVector_reconstruction (a : R)
    {L : CochainComplex (ModuleCat.{u} R) ℤ} (v : L ⟶ cochainCyclicThree U)
    (hv : v ≫ cochainCyclicThreeRotation U = a • v) :
    (v ≫ biprod.fst) ≫ cochainCyclicThreeVector U a = v := by
  have h₂ : v ≫ biprod.snd ≫ biprod.snd = a • (v ≫ biprod.fst) := by
    simpa only [cochainCyclicThreeRotation, Category.assoc, biprod.lift_fst,
      Linear.smul_comp] using hv =≫ biprod.fst
  have h₁ : v ≫ biprod.snd ≫ biprod.fst = a ^ 2 • (v ≫ biprod.fst) := by
    have h : v ≫ biprod.snd ≫ biprod.fst = a • (v ≫ biprod.snd ≫ biprod.snd) := by
      simpa only [cochainCyclicThreeRotation, Category.assoc, biprod.lift_snd_assoc,
        biprod.lift_snd, Linear.smul_comp] using hv =≫ (biprod.snd ≫ biprod.snd)
    rw [h, h₂, smul_smul, ← pow_two]
  apply biprod.hom_ext
  · simp only [Category.assoc, cochainCyclicThreeVector, biprod.lift_fst, comp_id]
  · apply biprod.hom_ext
    · simpa only [Category.assoc, cochainCyclicThreeVector, biprod.lift_snd_assoc,
        biprod.lift_fst, Linear.comp_smul, comp_id] using h₁.symm
    · simpa only [Category.assoc, cochainCyclicThreeVector, biprod.lift_snd_assoc,
        biprod.lift_snd, Linear.comp_smul, comp_id] using h₂.symm

/-- Every Fourier eigenspace of the standard three-copy action is the original complex. -/
def cochainCyclicThreeEigenIso [Invertible (3 : R)] (a : R) (ha : a ^ 3 = 1) :
    ((cochainCyclicThreeAction U).projector a ha).image ≅ U where
  hom := ((cochainCyclicThreeAction U).projector a ha).inclusion ≫ biprod.fst
  inv := (cochainCyclicThreeAction U).eigenvectorLift a ha (cochainCyclicThreeVector U a)
    (cochainCyclicThreeVector_eigen U a ha)
  hom_inv_id := by
    apply (cancel_mono ((cochainCyclicThreeAction U).projector a ha).inclusion).mp
    rw [Category.assoc, CochainCubicAction.eigenvectorLift_inclusion, id_comp]
    exact cochainCyclicThreeVector_reconstruction U a _
      ((cochainCyclicThreeAction U).projector_inclusion_eigen a ha)
  inv_hom_id := by
    rw [← Category.assoc, CochainCubicAction.eigenvectorLift_inclusion,
      cochainCyclicThreeVector_first]

end SerrePositivity

end CochainCyclicThreePart

section TensorTripleCyclicSumPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]

abbrev cochainTensorCyclicSum (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) :=
  cochainTensor (cochainTensor P Q) T ⊞
    (cochainTensor (cochainTensor T P) Q ⊞ cochainTensor (cochainTensor Q T) P)

def cochainTensorCyclicSumRotation (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensorCyclicSum P Q T ⟶ cochainTensorCyclicSum P Q T :=
  biprod.lift (biprod.snd ≫ biprod.snd ≫ (cochainTensorRotationIso Q T P).hom)
    (biprod.lift (biprod.fst ≫ (cochainTensorRotationIso P Q T).hom)
      (biprod.snd ≫ biprod.fst ≫ (cochainTensorRotationIso T P Q).hom))

lemma cochainTensorCyclicSumRotation_cube (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensorCyclicSumRotation P Q T ≫ cochainTensorCyclicSumRotation P Q T ≫
      cochainTensorCyclicSumRotation P Q T = 𝟙 _ := by
  apply biprod.hom_ext
  · simp only [cochainTensorCyclicSumRotation, Category.assoc, biprod.lift_fst,
      biprod.lift_fst_assoc, biprod.lift_snd_assoc,
      cochainTensorRotation_cube, comp_id, id_comp]
  · apply biprod.hom_ext
    · simp only [cochainTensorCyclicSumRotation, Category.assoc, biprod.lift_fst,
        biprod.lift_fst_assoc, biprod.lift_snd_assoc, biprod.lift_snd,
        cochainTensorRotation_cube, comp_id, id_comp]
    · simp only [cochainTensorCyclicSumRotation, Category.assoc,
        biprod.lift_fst_assoc, biprod.lift_snd_assoc, biprod.lift_snd,
        cochainTensorRotation_cube, comp_id, id_comp]

def cochainTensorCyclicSumAction (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainCubicAction (cochainTensorCyclicSum P Q T) :=
  ⟨cochainTensorCyclicSumRotation P Q T, cochainTensorCyclicSumRotation_cube P Q T⟩

end SerrePositivity

end TensorTripleCyclicSumPart

section TensorTripleCyclicSumPerfectPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
variable {R : Type u} [CommRing R]
variable (P Q T : CochainComplex (ModuleCat.{u} R) ℤ)

lemma cochainTensorCyclicSum_perfect
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
    (ht : strictlyPerfectComplex R T) :
    strictlyPerfectComplex R (cochainTensorCyclicSum P Q T) :=
  strictlyPerfectComplex_biprod
    (strictlyPerfectComplex_cochainTensor _ _ (strictlyPerfectComplex_cochainTensor _ _ hp hq) ht)
    (strictlyPerfectComplex_biprod
      (strictlyPerfectComplex_cochainTensor _ _ (strictlyPerfectComplex_cochainTensor _ _ ht hp) hq)
      (strictlyPerfectComplex_cochainTensor _ _
        (strictlyPerfectComplex_cochainTensor _ _ hq ht) hp))

lemma cochainTensorCyclicSum_support
    {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
    (ht : strictlyPerfectComplex R T)
    (hsP : HasHomologySupportOn Z P) (hsQ : HasHomologySupportOn Z Q)
    (hsT : HasHomologySupportOn Z T) : HasHomologySupportOn Z (cochainTensorCyclicSum P Q T) :=
  ((hsP.cochainTensor_left hp Q).cochainTensor_left
    (strictlyPerfectComplex_cochainTensor _ _ hp hq) T).biprod
    (((hsT.cochainTensor_left ht P).cochainTensor_left
      (strictlyPerfectComplex_cochainTensor _ _ ht hp) Q).biprod
      ((hsQ.cochainTensor_left hq T).cochainTensor_left
        (strictlyPerfectComplex_cochainTensor _ _ hq ht) P))

end SerrePositivity

end TensorTripleCyclicSumPerfectPart

section TensorTripleCyclicSumEigenPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]
variable (P Q T : CochainComplex (ModuleCat.{u} R) ℤ)

/-- Align the three tensor rotations with the first tensor complex. -/
def cochainTensorCyclicSumStandardIso : cochainTensorCyclicSum P Q T ≅
    cochainCyclicThree (cochainTensor (cochainTensor P Q) T) :=
  biprod.mapIso (Iso.refl _) (biprod.mapIso (cochainTensorRotationIso P Q T).symm
    ((cochainTensorRotationIso P Q T) ≪≫ (cochainTensorRotationIso T P Q)).symm)

lemma cochainTensorCyclicSumStandardIso_rotation :
    cochainTensorCyclicSumRotation P Q T ≫ (cochainTensorCyclicSumStandardIso P Q T).hom =
      (cochainTensorCyclicSumStandardIso P Q T).hom ≫
        cochainCyclicThreeRotation (cochainTensor (cochainTensor P Q) T) := by
  have hr : (cochainTensorRotationIso Q T P).hom =
      ((cochainTensorRotationIso P Q T) ≪≫ (cochainTensorRotationIso T P Q)).inv := by
    apply (cancel_epi
      ((cochainTensorRotationIso P Q T) ≪≫ (cochainTensorRotationIso T P Q)).hom).mp
    rw [Iso.hom_inv_id]
    simpa only [Iso.trans_hom, Category.assoc] using cochainTensorRotation_cube P Q T
  apply biprod.hom_ext
  · simp [cochainTensorCyclicSumStandardIso, cochainTensorCyclicSumRotation,
      cochainCyclicThreeRotation, biprod.mapIso, Category.assoc, hr]
  · apply biprod.hom_ext
    · simp [cochainTensorCyclicSumStandardIso, cochainTensorCyclicSumRotation,
        cochainCyclicThreeRotation, biprod.mapIso, Category.assoc]
    · simp [cochainTensorCyclicSumStandardIso, cochainTensorCyclicSumRotation,
        cochainCyclicThreeRotation, biprod.mapIso, Category.assoc]

/-- Every Fourier eigenspace of a cyclic tensor orbit is the first tensor summand. -/
def cochainTensorCyclicSumEigenIso [Invertible (3 : R)] (a : R) (ha : a ^ 3 = 1) :
    ((cochainTensorCyclicSumAction P Q T).projector a ha).image ≅
      cochainTensor (cochainTensor P Q) T :=
  CochainIdempotent.imageIso ((cochainTensorCyclicSumAction P Q T).projector a ha)
    ((cochainCyclicThreeAction (cochainTensor (cochainTensor P Q) T)).projector a ha)
    (cochainTensorCyclicSumStandardIso P Q T)
    ((cochainTensorCyclicSumAction P Q T).projectorMap_naturality
      (cochainCyclicThreeAction (cochainTensor (cochainTensor P Q) T))
      (cochainTensorCyclicSumStandardIso P Q T).hom
      (cochainTensorCyclicSumStandardIso_rotation P Q T) a) ≪≫
    cochainCyclicThreeEigenIso (cochainTensor (cochainTensor P Q) T) a ha

end SerrePositivity

end TensorTripleCyclicSumEigenPart

section TensorTripleCyclicSumClassPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits TensorProduct
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
variable (P Q T : CochainComplex (ModuleCat.{u} R) ℤ)
variable (t : R) (ht : t ^ 2 + t + 1 = 0)
variable (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
variable (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
    (hT : strictlyPerfectComplex R T)
variable (hsP : HasHomologySupportOn Z P) (hsQ : HasHomologySupportOn Z Q)
    (hsT : HasHomologySupportOn Z T)

lemma cochainTensorCyclicSum_eigenK0Class (j : Fin 3) :
    (cochainTensorCyclicSumAction P Q T).eigenK0Class t ht Z
      (cochainTensorCyclicSum_perfect P Q T hp hq hT)
      (cochainTensorCyclicSum_support P Q T hp hq hT hsP hsQ hsT) j =
    K0WithSupport.mk Z (supportedPerfectOnObj Z (cochainTensor (cochainTensor P Q) T)
      (strictlyPerfectComplex_cochainTensor _ _
        (strictlyPerfectComplex_cochainTensor _ _ hp hq) hT)
      ((hsP.cochainTensor_left hp Q).cochainTensor_left
        (strictlyPerfectComplex_cochainTensor _ _ hp hq) T)) := by
  let e := cochainTensorCyclicSumEigenIso P Q T (cubicCharacter t j)
    (cubicCharacter_cube t (cube_eq_one_of_cubic_relation t ht) j)
  exact K0WithSupport.mk_eq_of_quasiIso Z _ _
    (((cochainTensorCyclicSumAction P Q T).characterProjector t
      (cube_eq_one_of_cubic_relation t ht) j).image_strictlyPerfect
      (cochainTensorCyclicSum_perfect P Q T hp hq hT))
    (strictlyPerfectComplex_cochainTensor _ _
      (strictlyPerfectComplex_cochainTensor _ _ hp hq) hT)
    (((cochainTensorCyclicSumAction P Q T).characterProjector t
      (cube_eq_one_of_cubic_relation t ht) j).image_support
      (cochainTensorCyclicSum_support P Q T hp hq hT hsP hsQ hsT))
    ((hsP.cochainTensor_left hp Q).cochainTensor_left
      (strictlyPerfectComplex_cochainTensor _ _ hp hq) T) e.hom

lemma cochainTensorCyclicSum_weightedK0Class_eq_zero
    (E : Type v) [CommRing E] (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0) :
    (cochainTensorCyclicSumAction P Q T).weightedK0Class E t ht ζ Z
      (cochainTensorCyclicSum_perfect P Q T hp hq hT)
      (cochainTensorCyclicSum_support P Q T hp hq hT hsP hsQ hsT) = 0 := by
  unfold CochainCubicAction.weightedK0Class
  simp_rw [cochainTensorCyclicSum_eigenK0Class P Q T t ht Z hp hq hT hsP hsQ hsT]
  rw [← TensorProduct.sum_tmul, sum_cubicCharacter ζ hζ, TensorProduct.zero_tmul]

end SerrePositivity

end TensorTripleCyclicSumClassPart
