module

public import SerrePositivity.PerfectComplex.CubicActionTensorEigen
public import SerrePositivity.PerfectComplex.CubicActionClass
public import SerrePositivity.PerfectComplex.FinThreeBiproduct

/-! # The convolution formula for K₀ classes of tensor eigenspaces -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity
open CategoryTheory Category Limits TensorProduct
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace CochainCubicAction
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

lemma eigenK0Class_tensor (τ : CochainCubicAction K) (σ : CochainCubicAction L)
    (t : R) (ht : t ^ 2 + t + 1 = 0)
    (Y Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hpK : strictlyPerfectComplex R K) (hpL : strictlyPerfectComplex R L)
    (hsK : HasHomologySupportOn Y K) (hsL : HasHomologySupportOn Z L) (l : Fin 3) :
    (τ.tensor σ).eigenK0Class t ht (Y ⊓ Z)
      (strictlyPerfectComplex_cochainTensor K L hpK hpL) (hsK.cochainTensor hsL hpK hpL) l =
      ∑ i : Fin 3, K0WithSupport.cup (τ.eigenK0Class t ht Y hpK hsK i)
        (σ.eigenK0Class t ht Z hpL hsL (l - i)) := by
  let a := fun i => τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) i
  let b := fun i => σ.characterProjector t (cube_eq_one_of_cubic_relation t ht) i
  let W := fun i : Fin 3 => cochainTensor (a i).image (b (l - i)).image
  have hpW : ∀ i, strictlyPerfectComplex R (W i) := fun i =>
    strictlyPerfectComplex_cochainTensor _ _ ((a i).image_strictlyPerfect hpK)
      ((b (l - i)).image_strictlyPerfect hpL)
  have hsW : ∀ i, HasHomologySupportOn (Y ⊓ Z) (W i) := fun i =>
    ((a i).image_support hsK).cochainTensor ((b (l - i)).image_support hsL)
      ((a i).image_strictlyPerfect hpK) ((b (l - i)).image_strictlyPerfect hpL)
  let d := (τ.tensor σ).characterProjector t (cube_eq_one_of_cubic_relation t ht) l
  have hd := d.image_strictlyPerfect (strictlyPerfectComplex_cochainTensor K L hpK hpL)
  have sd := d.image_support (hsK.cochainTensor hsL hpK hpL)
  have h := K0WithSupport.mk_eq_of_quasiIso (Y ⊓ Z) (⨁ W) d.image
    (cochainFinThreeBiproduct_perfect W hpW) hd (cochainFinThreeBiproduct_support W hsW) sd
    (tensorCharacterEigenIso τ σ t ht l).hom
  change K0WithSupport.mk (Y ⊓ Z) (supportedPerfectOnObj (Y ⊓ Z) d.image hd sd) = _
  rw [← h, K0WithSupport.mk_finThreeBiproduct (Y ⊓ Z) W hpW hsW]
  apply Finset.sum_congr rfl
  intro i _
  exact K0WithSupport.mk_tensor (a i).image (b (l - i)).image
    ((a i).image_strictlyPerfect hpK) ((b (l - i)).image_strictlyPerfect hpL)
    ((a i).image_support hsK) ((b (l - i)).image_support hsL)

/-- Weighted tensor eigenspaces multiply by character convolution. -/
lemma weightedK0Class_tensor (E : Type v) [CommRing E]
    (τ : CochainCubicAction K) (σ : CochainCubicAction L)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (Y Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hpK : strictlyPerfectComplex R K) (hpL : strictlyPerfectComplex R L)
    (hsK : HasHomologySupportOn Y K) (hsL : HasHomologySupportOn Z L) :
    (τ.tensor σ).weightedK0Class E t ht ζ (Y ⊓ Z)
      (strictlyPerfectComplex_cochainTensor K L hpK hpL) (hsK.cochainTensor hsL hpK hpL) =
      K0WithSupport.coefficientCup E (τ.weightedK0Class E t ht ζ Y hpK hsK)
        (σ.weightedK0Class E t ht ζ Z hpL hsL) := by
  classical
  unfold weightedK0Class
  simp_rw [eigenK0Class_tensor τ σ t ht Y Z hpK hpL hsK hsL,
    TensorProduct.tmul_sum]
  rw [Finset.sum_comm]
  simp only [map_sum, LinearMap.sum_apply, K0WithSupport.coefficientCup_tmul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  symm
  apply Fintype.sum_equiv (Equiv.addLeft i)
  intro j
  change (cubicCharacter ζ i * cubicCharacter ζ j) ⊗ₜ[ℤ]
    K0WithSupport.cup (τ.eigenK0Class t ht Y hpK hsK i)
      (σ.eigenK0Class t ht Z hpL hsL j) =
    cubicCharacter ζ (i + j) ⊗ₜ[ℤ]
      K0WithSupport.cup (τ.eigenK0Class t ht Y hpK hsK i)
        (σ.eigenK0Class t ht Z hpL hsL (i + j - i))
  rw [add_sub_cancel_left]
  rw [cubicCharacter_mul ζ (cube_eq_one_of_cubic_relation ζ hζ)]

end CochainCubicAction
end SerrePositivity
