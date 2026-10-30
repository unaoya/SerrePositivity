module

public import SerrePositivity.PerfectComplex.InvolutionMaps
public import SerrePositivity.PerfectComplex.IdempotentImagePerfect
public import Mathlib.Algebra.Homology.QuasiIso
public import SerrePositivity.HomologicalAlgebra.Complex.Idempotent
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Exactness of positive and negative eigenspace sequences -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace CochainInvolution
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
  (t₁ : CochainInvolution S.X₁) (t₂ : CochainInvolution S.X₂) (t₃ : CochainInvolution S.X₃)
  (hf : t₁.map ≫ S.f = S.f ≫ t₂.map) (hg : t₂.map ≫ S.g = S.g ≫ t₃.map)

/-- The positive eigenspaces of an equivariant short complex. -/
abbrev positiveShortComplex :=
  CochainIdempotent.imageShortComplex S t₁.positive t₂.positive t₃.positive
    (positive_naturality t₁ t₂ S.f hf) (positive_naturality t₂ t₃ S.g hg)

/-- The negative eigenspaces of an equivariant short complex. -/
abbrev negativeShortComplex :=
  CochainIdempotent.imageShortComplex S t₁.negative t₂.negative t₃.negative
    (negative_naturality t₁ t₂ S.f hf) (negative_naturality t₂ t₃ S.g hg)

lemma positiveShortComplex_shortExact (hS : S.ShortExact) :
    (positiveShortComplex S t₁ t₂ t₃ hf hg).ShortExact :=
  CochainIdempotent.imageShortComplex_shortExact _ _ _ _ _ _ hS

lemma negativeShortComplex_shortExact (hS : S.ShortExact) :
    (negativeShortComplex S t₁ t₂ t₃ hf hg).ShortExact :=
  CochainIdempotent.imageShortComplex_shortExact _ _ _ _ _ _ hS

end CochainInvolution
end SerrePositivity
