module

public import SerrePositivity.KTheory.Adams.TensorSquareMixedCancellation
public import SerrePositivity.PerfectComplex.InvolutionClassShortExact

/-! # Additivity of the cyclic tensor-square class -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace Adams

/-- The class of the positive tensor square minus the class of the negative tensor square. -/
def tensorSquareClass (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P) : K0WithSupport Z :=
  (tensorSquareInvolution P).k0Class Z (tensorSquare_perfect P hp) (tensorSquare_support hp hs)

lemma tensorSquareClass_shortExact
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (ha : strictlyPerfectComplex R S.X₁) (hp : strictlyPerfectComplex R S.X₂)
    (hd : strictlyPerfectComplex R S.X₃)
    (hsA : HasHomologySupportOn Z S.X₁) (hsP : HasHomologySupportOn Z S.X₂)
    (hsD : HasHomologySupportOn Z S.X₃) :
    tensorSquareClass S.X₂ Z hp hsP =
      tensorSquareClass S.X₁ Z ha hsA + tensorSquareClass S.X₃ Z hd hsD := by
  let hproj := fun i => (hd.2 i).2
  have hout := CochainInvolution.k0Class_shortExact Z (tensorSquareKernelShortComplex S.g)
    (tensorSquareKernelInvolution S.g) (tensorSquareInvolution S.X₂) (tensorSquareInvolution S.X₃)
    (tensorSquareKernelSwap_inclusion S.g) (tensorSquareSwap_naturality S.g).symm
    (tensorSquareKernelShortComplex_shortExact S hS hproj)
    (tensorSquareKernel_perfect S hS hp hd) (tensorSquare_perfect S.X₂ hp)
    (tensorSquare_perfect S.X₃ hd) (tensorSquareKernel_support S hS hp hd hsP hsD)
    (tensorSquare_support hp hsP) (tensorSquare_support hd hsD)
  have hin := CochainInvolution.k0Class_shortExact Z (tensorSquareMixedShortComplex S hS hproj)
    (tensorSquareInvolution S.X₁) (tensorSquareKernelInvolution S.g) (tensorSquareMixedInvolution S)
    (tensorSquareKernelFirstMap_swap S).symm (tensorSquareMixedMap_swap S hS hproj)
    (tensorSquareMixedShortComplex_shortExact S hS hproj)
    (tensorSquare_perfect S.X₁ ha) (tensorSquareKernel_perfect S hS hp hd)
    (tensorSquareMixed_perfect S ha hd) (tensorSquare_support ha hsA)
    (tensorSquareKernel_support S hS hp hd hsP hsD) (tensorSquareMixed_support S ha hd hsA hsD)
  dsimp only [tensorSquareKernelShortComplex, tensorSquareMixedShortComplex] at hout hin
  dsimp only [tensorSquareClass]
  rw [hout, hin, tensorSquareMixed_k0Class_eq_zero S Z ha hd hsA hsD, add_zero]

end Adams
end SerrePositivity
