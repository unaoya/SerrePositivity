module

public import SerrePositivity.PerfectComplex.CubicActionClass
public import SerrePositivity.PerfectComplex.IdempotentImageShortExact

/-! # Additivity of weighted cubic classes on equivariant short exact sequences -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity
open CategoryTheory Category Limits TensorProduct
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace CochainCubicAction
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
variable (τ₁ : CochainCubicAction S.X₁) (τ₂ : CochainCubicAction S.X₂)
    (τ₃ : CochainCubicAction S.X₃)
variable (hf : τ₁.map ≫ S.f = S.f ≫ τ₂.map) (hg : τ₂.map ≫ S.g = S.g ≫ τ₃.map)
variable (t : R) (ht : t ^ 2 + t + 1 = 0)

/-- Restrict an equivariant short complex to one cubic character. -/
abbrev characterShortComplex (j : Fin 3) :=
  CochainIdempotent.imageShortComplex S
    (τ₁.characterProjector t (cube_eq_one_of_cubic_relation t ht) j)
    (τ₂.characterProjector t (cube_eq_one_of_cubic_relation t ht) j)
    (τ₃.characterProjector t (cube_eq_one_of_cubic_relation t ht) j)
    (τ₁.projectorMap_naturality τ₂ S.f hf (cubicCharacter t j))
    (τ₂.projectorMap_naturality τ₃ S.g hg (cubicCharacter t j))

lemma characterShortComplex_shortExact (j : Fin 3) (hS : S.ShortExact) :
    (characterShortComplex S τ₁ τ₂ τ₃ hf hg t ht j).ShortExact :=
  CochainIdempotent.imageShortComplex_shortExact _ _ _ _ _ _ hS

include hf hg in
lemma eigenK0Class_shortExact
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (j : Fin 3) (hS : S.ShortExact)
    (hp₁ : strictlyPerfectComplex R S.X₁) (hp₂ : strictlyPerfectComplex R S.X₂)
    (hp₃ : strictlyPerfectComplex R S.X₃)
    (hs₁ : HasHomologySupportOn Z S.X₁) (hs₂ : HasHomologySupportOn Z S.X₂)
    (hs₃ : HasHomologySupportOn Z S.X₃) :
    τ₂.eigenK0Class t ht Z hp₂ hs₂ j =
      τ₁.eigenK0Class t ht Z hp₁ hs₁ j + τ₃.eigenK0Class t ht Z hp₃ hs₃ j := by
  have h := K0WithSupport.mk_shortExact Z (characterShortComplex S τ₁ τ₂ τ₃ hf hg t ht j)
    (characterShortComplex_shortExact S τ₁ τ₂ τ₃ hf hg t ht j hS)
    ((τ₁.characterProjector t (cube_eq_one_of_cubic_relation t ht) j).image_strictlyPerfect hp₁)
    ((τ₂.characterProjector t (cube_eq_one_of_cubic_relation t ht) j).image_strictlyPerfect hp₂)
    ((τ₃.characterProjector t (cube_eq_one_of_cubic_relation t ht) j).image_strictlyPerfect hp₃)
    ((τ₁.characterProjector t (cube_eq_one_of_cubic_relation t ht) j).image_support hs₁)
    ((τ₂.characterProjector t (cube_eq_one_of_cubic_relation t ht) j).image_support hs₂)
    ((τ₃.characterProjector t (cube_eq_one_of_cubic_relation t ht) j).image_support hs₃)
  exact h

include hf hg in
lemma weightedK0Class_shortExact (E : Type v) [CommRing E] (ζ : E)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (hS : S.ShortExact)
    (hp₁ : strictlyPerfectComplex R S.X₁) (hp₂ : strictlyPerfectComplex R S.X₂)
    (hp₃ : strictlyPerfectComplex R S.X₃)
    (hs₁ : HasHomologySupportOn Z S.X₁) (hs₂ : HasHomologySupportOn Z S.X₂)
    (hs₃ : HasHomologySupportOn Z S.X₃) :
    τ₂.weightedK0Class E t ht ζ Z hp₂ hs₂ =
      τ₁.weightedK0Class E t ht ζ Z hp₁ hs₁ + τ₃.weightedK0Class E t ht ζ Z hp₃ hs₃ := by
  unfold weightedK0Class
  simp_rw [eigenK0Class_shortExact S τ₁ τ₂ τ₃ hf hg t ht Z _ hS hp₁ hp₂ hp₃ hs₁ hs₂ hs₃]
  simp only [TensorProduct.tmul_add, Finset.sum_add_distrib]

end CochainCubicAction
end SerrePositivity
