module

public import SerrePositivity.PerfectComplex.InvolutionClass
public import SerrePositivity.PerfectComplex.InvolutionShortExact

/-! # Additivity of eigenspace class differences on equivariant short exact sequences -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace CochainInvolution

lemma k0Class_shortExact
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (t₁ : CochainInvolution S.X₁) (t₂ : CochainInvolution S.X₂) (t₃ : CochainInvolution S.X₃)
    (hf : t₁.map ≫ S.f = S.f ≫ t₂.map) (hg : t₂.map ≫ S.g = S.g ≫ t₃.map)
    (hS : S.ShortExact)
    (hp₁ : strictlyPerfectComplex R S.X₁) (hp₂ : strictlyPerfectComplex R S.X₂)
    (hp₃ : strictlyPerfectComplex R S.X₃)
    (hs₁ : HasHomologySupportOn Z S.X₁) (hs₂ : HasHomologySupportOn Z S.X₂)
    (hs₃ : HasHomologySupportOn Z S.X₃) :
    t₂.k0Class Z hp₂ hs₂ = t₁.k0Class Z hp₁ hs₁ + t₃.k0Class Z hp₃ hs₃ := by
  have hpos := CochainIdempotent.k0Class_shortExact S t₁.positive t₂.positive t₃.positive
    (positive_naturality t₁ t₂ S.f hf) (positive_naturality t₂ t₃ S.g hg)
    Z hS hp₁ hp₂ hp₃ hs₁ hs₂ hs₃
  have hneg := CochainIdempotent.k0Class_shortExact S t₁.negative t₂.negative t₃.negative
    (negative_naturality t₁ t₂ S.f hf) (negative_naturality t₂ t₃ S.g hg)
    Z hS hp₁ hp₂ hp₃ hs₁ hs₂ hs₃
  unfold k0Class
  rw [hpos, hneg]
  abel

end CochainInvolution
end SerrePositivity
