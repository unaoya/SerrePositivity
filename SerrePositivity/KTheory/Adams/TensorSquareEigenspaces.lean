module

public import SerrePositivity.KTheory.Adams.TensorSquare
public import SerrePositivity.PerfectComplex.Eigen.Involution

/-! # Positive and negative tensor-square complexes -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]

namespace Adams

/-- The signed tensor-square exchange as an involution. -/
def tensorSquareInvolution (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainInvolution (tensorSquare P) := ⟨tensorSquareSwap P, tensorSquareSwap_sq P⟩

variable [Invertible (2 : R)]

/-- The positive tensor-square projector. -/
abbrev tensorSquarePositiveProjector (P : CochainComplex (ModuleCat.{u} R) ℤ) :=
  (tensorSquareInvolution P).positive

/-- The negative tensor-square projector. -/
abbrev tensorSquareNegativeProjector (P : CochainComplex (ModuleCat.{u} R) ℤ) :=
  (tensorSquareInvolution P).negative

/-- The positive part of the tensor square. -/
abbrev tensorSquarePositive (P : CochainComplex (ModuleCat.{u} R) ℤ) :=
  (tensorSquarePositiveProjector P).image

/-- The negative part of the tensor square. -/
abbrev tensorSquareNegative (P : CochainComplex (ModuleCat.{u} R) ℤ) :=
  (tensorSquareNegativeProjector P).image

lemma tensorSquarePositiveProjector_map (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tensorSquarePositiveProjector P).map = (⅟(2 : R)) • (𝟙 _ + tensorSquareSwap P) := rfl

lemma tensorSquareNegativeProjector_map (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tensorSquareNegativeProjector P).map = (⅟(2 : R)) • (𝟙 _ - tensorSquareSwap P) :=
  (tensorSquareInvolution P).negative_map

/-- The tensor square splits into its two eigenspaces. -/
def tensorSquareDecompositionIso (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    tensorSquarePositive P ⊞ tensorSquareNegative P ≅ tensorSquare P :=
  (tensorSquareInvolution P).decompositionIso

lemma tensorSquarePositive_perfect (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) : strictlyPerfectComplex R (tensorSquarePositive P) :=
  (tensorSquarePositiveProjector P).image_strictlyPerfect (tensorSquare_perfect P hp)

lemma tensorSquareNegative_perfect (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) : strictlyPerfectComplex R (tensorSquareNegative P) :=
  (tensorSquareNegativeProjector P).image_strictlyPerfect (tensorSquare_perfect P hp)

lemma tensorSquarePositive_support {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (hp : strictlyPerfectComplex R P)
    (hs : HasHomologySupportOn Z P) : HasHomologySupportOn Z (tensorSquarePositive P) :=
  (tensorSquarePositiveProjector P).image_support (tensorSquare_support hp hs)

lemma tensorSquareNegative_support {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (hp : strictlyPerfectComplex R P)
    (hs : HasHomologySupportOn Z P) : HasHomologySupportOn Z (tensorSquareNegative P) :=
  (tensorSquareNegativeProjector P).image_support (tensorSquare_support hp hs)

@[reassoc]
lemma tensorSquarePositive_inclusion_swap (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tensorSquarePositiveProjector P).inclusion ≫ tensorSquareSwap P =
      (tensorSquarePositiveProjector P).inclusion :=
  (tensorSquareInvolution P).positive_inclusion_map

@[reassoc]
lemma tensorSquareNegative_inclusion_swap (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tensorSquareNegativeProjector P).inclusion ≫ tensorSquareSwap P =
      -(tensorSquareNegativeProjector P).inclusion :=
  (tensorSquareInvolution P).negative_inclusion_map

end Adams
end SerrePositivity
