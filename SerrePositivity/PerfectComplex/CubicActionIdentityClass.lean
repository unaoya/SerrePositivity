module

public import SerrePositivity.PerfectComplex.CubicActionClassMaps

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

set_option backward.isDefEq.respectTransparency true in
lemma characterProjector_zero_of_map_eq_id (τ : CochainCubicAction K)
    (hτ : τ.map = 𝟙 K) (t : R) (ht : t ^ 3 = 1) :
    (τ.characterProjector t ht 0).map = 𝟙 K := by
  change τ.projectorMap (cubicCharacter t 0) = 𝟙 K
  simp only [cubicCharacter, Fin.val_zero, pow_zero]
  rw [projectorMap, hτ, id_comp, one_pow, one_smul]
  have he : (𝟙 K : K ⟶ K) + 𝟙 K + 𝟙 K = (3 : R) • 𝟙 K := by module
  rw [he, smul_smul, invOf_mul_self, one_smul]

lemma characterProjector_nonzero_of_map_eq_id (τ : CochainCubicAction K)
    (hτ : τ.map = 𝟙 K) (t : R) (ht : t ^ 2 + t + 1 = 0)
    (j : Fin 3) (hj : j ≠ 0) :
    (τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) j).map = 0 := by
  have he := τ.characterProjector_orthogonal t ht 0 j hj.symm
  rw [characterProjector_zero_of_map_eq_id τ hτ t, id_comp] at he
  exact he

/-- The character-zero image of a trivial action is the original complex. -/
def characterZeroImageIsoOfMapEqId (τ : CochainCubicAction K)
    (hτ : τ.map = 𝟙 K) (t : R) (ht : t ^ 3 = 1) :
    (τ.characterProjector t ht 0).image ≅ K where
  hom := (τ.characterProjector t ht 0).inclusion
  inv := (τ.characterProjector t ht 0).projection
  hom_inv_id := (τ.characterProjector t ht 0).inclusion_projection
  inv_hom_id := by
    rw [CochainIdempotent.projection_inclusion, characterProjector_zero_of_map_eq_id τ hτ t ht]

lemma characterNonzeroImage_isZero_of_map_eq_id (τ : CochainCubicAction K)
    (hτ : τ.map = 𝟙 K) (t : R) (ht : t ^ 2 + t + 1 = 0)
    (j : Fin 3) (hj : j ≠ 0) :
    IsZero (τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) j).image := by
  let e := τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) j
  have hi : e.inclusion = 0 := by
    rw [← e.inclusion_map, characterProjector_nonzero_of_map_eq_id τ hτ t ht j hj, comp_zero]
  rw [IsZero.iff_id_eq_zero, ← e.inclusion_projection, hi, zero_comp]

lemma eigenK0Class_zero_of_map_eq_id (τ : CochainCubicAction K)
    (hτ : τ.map = 𝟙 K) (t : R) (ht : t ^ 2 + t + 1 = 0)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) :
    τ.eigenK0Class t ht Z hp hs 0 = K0WithSupport.mk Z (supportedPerfectOnObj Z K hp hs) :=
  K0WithSupport.mk_eq_of_quasiIso Z _ _
    ((τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) 0).image_strictlyPerfect hp) hp
    ((τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) 0).image_support hs) hs
    (characterZeroImageIsoOfMapEqId τ hτ t (cube_eq_one_of_cubic_relation t ht)).hom

lemma eigenK0Class_nonzero_of_map_eq_id (τ : CochainCubicAction K)
    (hτ : τ.map = 𝟙 K) (t : R) (ht : t ^ 2 + t + 1 = 0)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K)
    (j : Fin 3) (hj : j ≠ 0) : τ.eigenK0Class t ht Z hp hs j = 0 := by
  let e := τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) j
  have hz := characterNonzeroImage_isZero_of_map_eq_id τ hτ t ht j hj
  have hac : e.image.Acyclic := (cochainAcyclic_iff_support_bot _).mpr
    (hasHomologySupportOn_of_isZero hz)
  exact K0WithSupport.mk_eq_zero_of_acyclic Z (e.image_strictlyPerfect hp) (e.image_support hs) hac

lemma weightedK0Class_of_map_eq_id (E : Type v) [CommRing E] (τ : CochainCubicAction K)
    (hτ : τ.map = 𝟙 K) (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) :
    τ.weightedK0Class E t ht ζ Z hp hs =
      (1 : E) ⊗ₜ[ℤ] K0WithSupport.mk Z (supportedPerfectOnObj Z K hp hs) := by
  unfold weightedK0Class
  rw [Fin.sum_univ_three, eigenK0Class_zero_of_map_eq_id τ hτ t ht Z hp hs,
    eigenK0Class_nonzero_of_map_eq_id τ hτ t ht Z hp hs 1 (by decide),
    eigenK0Class_nonzero_of_map_eq_id τ hτ t ht Z hp hs 2 (by decide)]
  simp [cubicCharacter]

end CochainCubicAction
end SerrePositivity
