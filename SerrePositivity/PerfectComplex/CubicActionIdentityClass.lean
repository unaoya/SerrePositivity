module

public import SerrePositivity.PerfectComplex.CubicActionScalarClass

/-! # The weighted character class of a trivial cubic action -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity
open CategoryTheory Category Limits TensorProduct
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace CochainCubicAction
variable {K : CochainComplex (ModuleCat.{u} R) ℤ}

lemma characterProjector_zero_of_map_eq_id (τ : CochainCubicAction K)
    (hτ : τ.map = 𝟙 K) (t : R) (ht : t ^ 3 = 1) :
    (τ.characterProjector t ht 0).map = 𝟙 K := by
  exact τ.characterProjector_self_of_map_eq_scalar t ht 0 (by simpa [cubicCharacter] using hτ)

lemma characterProjector_nonzero_of_map_eq_id (τ : CochainCubicAction K)
    (hτ : τ.map = 𝟙 K) (t : R) (ht : t ^ 2 + t + 1 = 0)
    (j : Fin 3) (hj : j ≠ 0) :
    (τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) j).map = 0 := by
  exact τ.characterProjector_other_of_map_eq_scalar t ht 0 j
    (by simpa [cubicCharacter] using hτ) hj.symm

/-- The character-zero image of a trivial action is the original complex. -/
def characterZeroImageIsoOfMapEqId (τ : CochainCubicAction K)
    (hτ : τ.map = 𝟙 K) (t : R) (ht : t ^ 3 = 1) :
    (τ.characterProjector t ht 0).image ≅ K :=
  τ.characterSelfImageIsoOfMapEqScalar t ht 0 (by simpa [cubicCharacter] using hτ)

lemma characterNonzeroImage_isZero_of_map_eq_id (τ : CochainCubicAction K)
    (hτ : τ.map = 𝟙 K) (t : R) (ht : t ^ 2 + t + 1 = 0)
    (j : Fin 3) (hj : j ≠ 0) :
    IsZero (τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) j).image := by
  exact τ.characterOtherImage_isZero_of_map_eq_scalar t ht 0 j
    (by simpa [cubicCharacter] using hτ) hj.symm

lemma eigenK0Class_zero_of_map_eq_id (τ : CochainCubicAction K)
    (hτ : τ.map = 𝟙 K) (t : R) (ht : t ^ 2 + t + 1 = 0)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) :
    τ.eigenK0Class t ht Z hp hs 0 = K0WithSupport.mk Z (supportedPerfectOnObj Z K hp hs) :=
  τ.eigenK0Class_self_of_map_eq_scalar t ht 0 (by simpa [cubicCharacter] using hτ) Z hp hs

lemma eigenK0Class_nonzero_of_map_eq_id (τ : CochainCubicAction K)
    (hτ : τ.map = 𝟙 K) (t : R) (ht : t ^ 2 + t + 1 = 0)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K)
    (j : Fin 3) (hj : j ≠ 0) : τ.eigenK0Class t ht Z hp hs j = 0 := by
  exact τ.eigenK0Class_other_of_map_eq_scalar t ht 0 j
    (by simpa [cubicCharacter] using hτ) Z hp hs hj.symm

lemma weightedK0Class_of_map_eq_id (E : Type v) [CommRing E] (τ : CochainCubicAction K)
    (hτ : τ.map = 𝟙 K) (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) :
    τ.weightedK0Class E t ht ζ Z hp hs =
      (1 : E) ⊗ₜ[ℤ] K0WithSupport.mk Z (supportedPerfectOnObj Z K hp hs) := by
  simpa only [cubicCharacter, Fin.val_zero, pow_zero] using
    weightedK0Class_of_map_eq_scalar E τ t ht 0 (by simpa [cubicCharacter] using hτ) ζ Z hp hs

end CochainCubicAction
end SerrePositivity
