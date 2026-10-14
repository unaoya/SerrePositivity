module

public import SerrePositivity.PerfectComplex.TensorShuffleEquivariance
public import SerrePositivity.KTheory.Adams.TensorSquareEigenspaces
public import SerrePositivity.PerfectComplex.InvolutionTensor
public import SerrePositivity.PerfectComplex.IdempotentImageIso

/-! # The equivariant shuffle used for multiplicativity of the cyclic square -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R]
namespace Adams

def tensorSquareTensorIso (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    tensorSquare (cochainTensor P Q) ≅ cochainTensor (tensorSquare P) (tensorSquare Q) :=
  cochainTensorShuffle P Q P Q

abbrev tensorSquareDiagonalSwap (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :=
  cochainTensorMap (tensorSquareSwap P) (tensorSquareSwap Q)

lemma tensorSquareDiagonalSwap_sq (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    tensorSquareDiagonalSwap P Q ≫ tensorSquareDiagonalSwap P Q = 𝟙 _ := by
  rw [cochainTensorMap_comp, tensorSquareSwap_sq, tensorSquareSwap_sq, cochainTensorMap_id]

def tensorSquareDiagonalInvolution (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainInvolution (cochainTensor (tensorSquare P) (tensorSquare Q)) :=
  ⟨tensorSquareDiagonalSwap P Q, tensorSquareDiagonalSwap_sq P Q⟩

/-- The signed shuffle identifies block exchange with the tensor of the two square exchanges. -/
lemma tensorSquareTensorIso_swap (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    tensorSquareSwap (cochainTensor P Q) ≫ (tensorSquareTensorIso P Q).hom =
      (tensorSquareTensorIso P Q).hom ≫ tensorSquareDiagonalSwap P Q :=
  cochainTensorShuffle_symmetry P Q P Q

lemma tensorSquareDiagonal_perfect (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q) :
    strictlyPerfectComplex R (cochainTensor (tensorSquare P) (tensorSquare Q)) :=
  strictlyPerfectComplex_cochainTensor _ _ (tensorSquare_perfect P hp) (tensorSquare_perfect Q hq)

lemma tensorSquareDiagonal_support
    {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
    (hsP : HasHomologySupportOn Y P) (hsQ : HasHomologySupportOn Z Q) :
    HasHomologySupportOn (Y ⊓ Z) (cochainTensor (tensorSquare P) (tensorSquare Q)) :=
  (tensorSquare_support hp hsP).cochainTensor (tensorSquare_support hq hsQ)
    (tensorSquare_perfect P hp) (tensorSquare_perfect Q hq)

variable [Invertible (2 : R)]

def tensorSquareTensorPositiveIso (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    tensorSquarePositive (cochainTensor P Q) ≅
      ((tensorSquareInvolution P).tensor (tensorSquareInvolution Q)).positive.image :=
  CochainIdempotent.imageIso (tensorSquarePositiveProjector (cochainTensor P Q))
    (((tensorSquareInvolution P).tensor (tensorSquareInvolution Q)).positive)
    (tensorSquareTensorIso P Q)
    (CochainInvolution.positive_naturality _ _ _ (tensorSquareTensorIso_swap P Q))

def tensorSquareTensorNegativeIso (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    tensorSquareNegative (cochainTensor P Q) ≅
      ((tensorSquareInvolution P).tensor (tensorSquareInvolution Q)).negative.image :=
  CochainIdempotent.imageIso (tensorSquareNegativeProjector (cochainTensor P Q))
    (((tensorSquareInvolution P).tensor (tensorSquareInvolution Q)).negative)
    (tensorSquareTensorIso P Q)
    (CochainInvolution.negative_naturality _ _ _ (tensorSquareTensorIso_swap P Q))

def tensorSquarePositiveFourIso (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensor (tensorSquarePositive P) (tensorSquarePositive Q) ⊞
      cochainTensor (tensorSquareNegative P) (tensorSquareNegative Q) ≅
        tensorSquarePositive (cochainTensor P Q) :=
  (CochainInvolution.positiveTensorIso (tensorSquareInvolution P) (tensorSquareInvolution Q)) ≪≫
    (tensorSquareTensorPositiveIso P Q).symm

def tensorSquareNegativeFourIso (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensor (tensorSquarePositive P) (tensorSquareNegative Q) ⊞
      cochainTensor (tensorSquareNegative P) (tensorSquarePositive Q) ≅
        tensorSquareNegative (cochainTensor P Q) :=
  (CochainInvolution.negativeTensorIso (tensorSquareInvolution P) (tensorSquareInvolution Q)) ≪≫
    (tensorSquareTensorNegativeIso P Q).symm

end Adams
end SerrePositivity
