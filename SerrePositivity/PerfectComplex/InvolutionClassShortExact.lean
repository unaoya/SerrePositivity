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
  have hpos := K0WithSupport.mk_shortExact Z (positiveShortComplex S t₁ t₂ t₃ hf hg)
    (positiveShortComplex_shortExact S t₁ t₂ t₃ hf hg hS)
    (t₁.positive.image_strictlyPerfect hp₁) (t₂.positive.image_strictlyPerfect hp₂)
    (t₃.positive.image_strictlyPerfect hp₃)
    (t₁.positive.image_support hs₁) (t₂.positive.image_support hs₂) (t₃.positive.image_support hs₃)
  have hneg := K0WithSupport.mk_shortExact Z (negativeShortComplex S t₁ t₂ t₃ hf hg)
    (negativeShortComplex_shortExact S t₁ t₂ t₃ hf hg hS)
    (t₁.negative.image_strictlyPerfect hp₁) (t₂.negative.image_strictlyPerfect hp₂)
    (t₃.negative.image_strictlyPerfect hp₃)
    (t₁.negative.image_support hs₁) (t₂.negative.image_support hs₂) (t₃.negative.image_support hs₃)
  dsimp [k0Class, positiveShortComplex, negativeShortComplex,
    CochainIdempotent.imageShortComplex] at hpos hneg ⊢
  rw [hpos, hneg]
  abel

end CochainInvolution
end SerrePositivity
