module

public import SerrePositivity.PerfectComplex.CubicActionClassMaps
public import SerrePositivity.PerfectComplex.CubicActionEigenvectors
public import SerrePositivity.PerfectComplex.CubicActionCharacter

/-! # Character classes of scalar cubic actions -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace SerrePositivity
open CategoryTheory Category Limits TensorProduct
variable {R : Type u} [CommRing R]
namespace CochainCubicAction
variable {K : CochainComplex (ModuleCat.{u} R) ℤ}

variable [Invertible (3 : R)]

lemma characterProjector_self_of_map_eq_scalar (τ : CochainCubicAction K)
    (t : R) (ht : t ^ 3 = 1) (j : Fin 3)
    (hτ : τ.map = cubicCharacter t j • 𝟙 K) :
    (τ.characterProjector t ht j).map = 𝟙 K := by
  have hf : (𝟙 K : K ⟶ K) ≫ τ.map = cubicCharacter t j • 𝟙 K := by
    rw [id_comp, hτ]
  change τ.projectorMap (cubicCharacter t j) = 𝟙 K
  simpa only [id_comp] using τ.eigenvector_comp_projectorMap
    (cubicCharacter t j) (cubicCharacter_cube t ht j) (𝟙 K) hf

lemma characterProjector_other_of_map_eq_scalar (τ : CochainCubicAction K)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (j k : Fin 3)
    (hτ : τ.map = cubicCharacter t j • 𝟙 K) (hne : j ≠ k) :
    (τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) k).map = 0 := by
  have he := τ.characterProjector_orthogonal t ht j k hne
  rw [characterProjector_self_of_map_eq_scalar τ t
    (cube_eq_one_of_cubic_relation t ht) j hτ, id_comp] at he
  exact he

/-- The matching character image of a scalar action is the original complex. -/
def characterSelfImageIsoOfMapEqScalar (τ : CochainCubicAction K)
    (t : R) (ht : t ^ 3 = 1) (j : Fin 3)
    (hτ : τ.map = cubicCharacter t j • 𝟙 K) :
    (τ.characterProjector t ht j).image ≅ K where
  hom := (τ.characterProjector t ht j).inclusion
  inv := (τ.characterProjector t ht j).projection
  hom_inv_id := (τ.characterProjector t ht j).inclusion_projection
  inv_hom_id := by
    rw [CochainIdempotent.projection_inclusion,
      characterProjector_self_of_map_eq_scalar τ t ht j hτ]

lemma characterOtherImage_isZero_of_map_eq_scalar (τ : CochainCubicAction K)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (j k : Fin 3)
    (hτ : τ.map = cubicCharacter t j • 𝟙 K) (hne : j ≠ k) :
    IsZero (τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) k).image := by
  let e := τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) k
  have hi : e.inclusion = 0 := by
    rw [← e.inclusion_map, characterProjector_other_of_map_eq_scalar τ t ht j k hτ hne,
      comp_zero]
  rw [IsZero.iff_id_eq_zero, ← e.inclusion_projection, hi, zero_comp]

lemma eigenK0Class_self_of_map_eq_scalar (τ : CochainCubicAction K)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (j : Fin 3)
    (hτ : τ.map = cubicCharacter t j • 𝟙 K)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) :
    τ.eigenK0Class t ht Z hp hs j = K0WithSupport.mk Z (supportedPerfectOnObj Z K hp hs) :=
  K0WithSupport.mk_eq_of_quasiIso Z _ _
    ((τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) j).image_strictlyPerfect hp) hp
    ((τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) j).image_support hs) hs
    (characterSelfImageIsoOfMapEqScalar τ t (cube_eq_one_of_cubic_relation t ht) j hτ).hom

lemma eigenK0Class_other_of_map_eq_scalar (τ : CochainCubicAction K)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (j k : Fin 3)
    (hτ : τ.map = cubicCharacter t j • 𝟙 K)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K)
    (hne : j ≠ k) : τ.eigenK0Class t ht Z hp hs k = 0 := by
  let e := τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) k
  have hz := characterOtherImage_isZero_of_map_eq_scalar τ t ht j k hτ hne
  have hac : e.image.Acyclic := (cochainAcyclic_iff_support_bot _).mpr
    (hasHomologySupportOn_of_isZero hz)
  exact K0WithSupport.mk_eq_zero_of_acyclic Z (e.image_strictlyPerfect hp) (e.image_support hs) hac

lemma weightedK0Class_of_map_eq_scalar (E : Type v) [CommRing E] (τ : CochainCubicAction K)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (j : Fin 3)
    (hτ : τ.map = cubicCharacter t j • 𝟙 K) (ζ : E)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) :
    τ.weightedK0Class E t ht ζ Z hp hs =
      cubicCharacter ζ j ⊗ₜ[ℤ] K0WithSupport.mk Z (supportedPerfectOnObj Z K hp hs) := by
  unfold weightedK0Class
  rw [Finset.sum_eq_single j]
  · rw [eigenK0Class_self_of_map_eq_scalar τ t ht j hτ Z hp hs]
  · intro k _ hkj
    rw [eigenK0Class_other_of_map_eq_scalar τ t ht j k hτ Z hp hs hkj.symm, tmul_zero]
  · simp

/-- A character scalar action contributes just its character times the original class. -/
@[simp]
lemma weightedK0Class_characterScalar (E : Type v) [CommRing E]
    (t : R) (ht : t ^ 2 + t + 1 = 0) (j : Fin 3) (ζ : E)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) :
    (characterScalar K t (cube_eq_one_of_cubic_relation t ht) j).weightedK0Class
        E t ht ζ Z hp hs =
      cubicCharacter ζ j ⊗ₜ[ℤ] K0WithSupport.mk Z (supportedPerfectOnObj Z K hp hs) :=
  weightedK0Class_of_map_eq_scalar E _ t ht j rfl ζ Z hp hs

end CochainCubicAction
end SerrePositivity
