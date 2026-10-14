module

public import SerrePositivity.PerfectComplex.TensorTripleCyclicSumEigen
public import SerrePositivity.PerfectComplex.CubicActionClass

/-! # Cancellation of the weighted class of a cyclic tensor orbit -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
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
