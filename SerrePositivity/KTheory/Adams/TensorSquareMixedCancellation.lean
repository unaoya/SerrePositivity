module

public import SerrePositivity.KTheory.Adams.TensorSquareMixedSplitting
public import SerrePositivity.PerfectComplex.InvolutionAntiEquivariance
public import SerrePositivity.PerfectComplex.InvolutionClass
public import SerrePositivity.PerfectComplex.BiproductPerfect

/-! # Cancellation of positive and negative mixed tensor components -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits Preadditive
variable {R : Type u} [CommRing R]

namespace Adams
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))

def tensorSquareMixedInvolution :
    CochainInvolution (cochainTensor S.X₁ S.X₃ ⊞ cochainTensor S.X₃ S.X₁) :=
  ⟨tensorSquareMixedSwap S, tensorSquareMixedSwap_sq S⟩

/-- Negate the second mixed component and preserve the first. -/
def tensorSquareMixedGrading : cochainTensor S.X₁ S.X₃ ⊞ cochainTensor S.X₃ S.X₁ ⟶
    cochainTensor S.X₁ S.X₃ ⊞ cochainTensor S.X₃ S.X₁ := biprod.map (𝟙 _) (-𝟙 _)

lemma tensorSquareMixedGrading_sq :
    tensorSquareMixedGrading S ≫ tensorSquareMixedGrading S = 𝟙 _ := by
  apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
    simp [tensorSquareMixedGrading, Category.assoc]

lemma tensorSquareMixedGrading_anticommute :
    tensorSquareMixedSwap S ≫ tensorSquareMixedGrading S =
      -(tensorSquareMixedGrading S ≫ tensorSquareMixedSwap S) := by
  apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
    simp [tensorSquareMixedSwap, tensorSquareMixedGrading, Category.assoc]

/-- The positive and negative mixed eigenspaces are chain isomorphic. -/
def tensorSquareMixedPositiveNegativeIso [Invertible (2 : R)] :
    (tensorSquareMixedInvolution S).positive.image ≅
      (tensorSquareMixedInvolution S).negative.image :=
  (tensorSquareMixedInvolution S).positiveNegativeIso (tensorSquareMixedGrading S)
    (tensorSquareMixedGrading_anticommute S) (tensorSquareMixedGrading_sq S)

lemma tensorSquareMixed_perfect
    (ha : strictlyPerfectComplex R S.X₁) (hd : strictlyPerfectComplex R S.X₃) :
    strictlyPerfectComplex R (cochainTensor S.X₁ S.X₃ ⊞ cochainTensor S.X₃ S.X₁) :=
  strictlyPerfectComplex_biprod
    (strictlyPerfectComplex_cochainTensor _ _ ha hd)
    (strictlyPerfectComplex_cochainTensor _ _ hd ha)

lemma tensorSquareMixed_support {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (ha : strictlyPerfectComplex R S.X₁) (hd : strictlyPerfectComplex R S.X₃)
    (hsA : HasHomologySupportOn Z S.X₁) (hsD : HasHomologySupportOn Z S.X₃) :
    HasHomologySupportOn Z (cochainTensor S.X₁ S.X₃ ⊞ cochainTensor S.X₃ S.X₁) :=
  (hsA.cochainTensor_left ha S.X₃).biprod (hsD.cochainTensor_left hd S.X₁)

lemma tensorSquareMixed_k0Class_eq_zero [Invertible (2 : R)]
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (ha : strictlyPerfectComplex R S.X₁) (hd : strictlyPerfectComplex R S.X₃)
    (hsA : HasHomologySupportOn Z S.X₁) (hsD : HasHomologySupportOn Z S.X₃) :
    (tensorSquareMixedInvolution S).k0Class Z (tensorSquareMixed_perfect S ha hd)
      (tensorSquareMixed_support S ha hd hsA hsD) = 0 :=
  (tensorSquareMixedInvolution S).k0Class_eq_zero_of_anticommute Z
    (tensorSquareMixed_perfect S ha hd) (tensorSquareMixed_support S ha hd hsA hsD)
    (tensorSquareMixedGrading S) (tensorSquareMixedGrading_anticommute S)
    (tensorSquareMixedGrading_sq S)

end Adams
end SerrePositivity
