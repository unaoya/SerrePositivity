module

public import SerrePositivity.HomologicalAlgebra.CochainTensorLinear
public import SerrePositivity.HomologicalAlgebra.CochainTensorDegreeMaps
public import SerrePositivity.PerfectComplex.TensorSupport
public import SerrePositivity.HomologicalAlgebra.CochainTensorShift
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import SerrePositivity.HomologicalAlgebra.CochainTensorShortExact
public import SerrePositivity.PerfectComplex.DegreewiseRetract
public import SerrePositivity.KTheory.Adams.TensorSquareEigenspaces

/-! # The intermediate layer of the tensor-square filtration -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

namespace Adams
variable {P D : CochainComplex (ModuleCat.{u} R) ℤ}

/-- The intermediate layer consists of tensors with at least one factor in the kernel. -/
abbrev tensorSquareKernel (q : P ⟶ D) := kernel (tensorSquareMap q)

abbrev tensorSquareKernelInclusion (q : P ⟶ D) : tensorSquareKernel q ⟶ tensorSquare P :=
  kernel.ι (tensorSquareMap q)

/-- Signed exchange preserves the intermediate layer. -/
def tensorSquareKernelSwap (q : P ⟶ D) : tensorSquareKernel q ⟶ tensorSquareKernel q :=
  kernel.lift (tensorSquareMap q) (tensorSquareKernelInclusion q ≫ tensorSquareSwap P) (by
    rw [Category.assoc, ← tensorSquareSwap_naturality, ← Category.assoc,
      kernel.condition, zero_comp])

@[simp, reassoc]
lemma tensorSquareKernelSwap_inclusion (q : P ⟶ D) :
    tensorSquareKernelSwap q ≫ tensorSquareKernelInclusion q =
      tensorSquareKernelInclusion q ≫ tensorSquareSwap P := kernel.lift_ι _ _ _

lemma tensorSquareKernelSwap_sq (q : P ⟶ D) :
    tensorSquareKernelSwap q ≫ tensorSquareKernelSwap q = 𝟙 _ := by
  apply (cancel_mono (tensorSquareKernelInclusion q)).1
  simp only [Category.assoc, tensorSquareKernelSwap_inclusion,
    tensorSquareKernelSwap_inclusion_assoc, tensorSquareSwap_sq, comp_id, id_comp]

def tensorSquareKernelInvolution (q : P ⟶ D) : CochainInvolution (tensorSquareKernel q) :=
  ⟨tensorSquareKernelSwap q, tensorSquareKernelSwap_sq q⟩

abbrev tensorSquareKernelShortComplex (q : P ⟶ D) :=
  ShortComplex.mk (tensorSquareKernelInclusion q) (tensorSquareMap q) (kernel.condition _)

lemma tensorSquareMap_epi_of_shortExact
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (hproj : ∀ i, Module.Projective R (S.X₃.X i)) : Epi (tensorSquareMap S.g) := by
  have hr := cochainTensorShortComplexRight_shortExact_of_projective S hS hproj S.X₂
  have hl := cochainTensorShortComplexLeft_shortExact_of_projective S.X₃ S hS hproj
  have : Epi (cochainTensorMap S.g (𝟙 S.X₂)) := hr.epi_g
  have : Epi (cochainTensorMap (𝟙 S.X₃) S.g) := hl.epi_g
  have he : cochainTensorMap S.g (𝟙 S.X₂) ≫ cochainTensorMap (𝟙 S.X₃) S.g =
      tensorSquareMap S.g := by
    rw [cochainTensorMap_comp, comp_id, id_comp]
  rw [← he]
  infer_instance

lemma tensorSquareKernelShortComplex_shortExact
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (hproj : ∀ i, Module.Projective R (S.X₃.X i)) :
    (tensorSquareKernelShortComplex S.g).ShortExact := by
  have := tensorSquareMap_epi_of_shortExact S hS hproj
  exact { exact := ShortComplex.exact_kernel (tensorSquareMap S.g) }

lemma tensorSquareKernel_perfect
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (hp : strictlyPerfectComplex R S.X₂) (hd : strictlyPerfectComplex R S.X₃) :
    strictlyPerfectComplex R (tensorSquareKernel S.g) :=
  strictlyPerfectComplex_of_shortExact (tensorSquareKernelShortComplex S.g)
    (tensorSquareKernelShortComplex_shortExact S hS (fun i => (hd.2 i).2))
    (tensorSquare_perfect S.X₂ hp) (fun i => ((tensorSquare_perfect S.X₃ hd).2 i).2)

lemma tensorSquareKernel_support
    {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (hp : strictlyPerfectComplex R S.X₂) (hd : strictlyPerfectComplex R S.X₃)
    (hsP : HasHomologySupportOn Z S.X₂) (hsD : HasHomologySupportOn Z S.X₃) :
    HasHomologySupportOn Z (tensorSquareKernel S.g) :=
  HasHomologySupportOn.of_shortExact (tensorSquareKernelShortComplex S.g)
    (tensorSquareKernelShortComplex_shortExact S hS (fun i => (hd.2 i).2))
    (tensorSquare_support hp hsP) (tensorSquare_support hd hsD)

/-- The tensor square of the first term maps into the intermediate layer. -/
def tensorSquareKernelFirstMap
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) :
    tensorSquare S.X₁ ⟶ tensorSquareKernel S.g :=
  kernel.lift (tensorSquareMap S.g) (tensorSquareMap S.f) (by
    rw [cochainTensorMap_comp, S.zero, cochainTensorMap_zero_zero])

@[simp, reassoc]
lemma tensorSquareKernelFirstMap_inclusion
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) :
    tensorSquareKernelFirstMap S ≫ tensorSquareKernelInclusion S.g = tensorSquareMap S.f :=
  kernel.lift_ι _ _ _

lemma tensorSquareMap_mono_of_shortExact
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (hproj : ∀ i, Module.Projective R (S.X₃.X i)) : Mono (tensorSquareMap S.f) := by
  have hr := cochainTensorShortComplexRight_shortExact_of_projective S hS hproj S.X₁
  have hl := cochainTensorShortComplexLeft_shortExact_of_projective S.X₂ S hS hproj
  have : Mono (cochainTensorMap S.f (𝟙 S.X₁)) := hr.mono_f
  have : Mono (cochainTensorMap (𝟙 S.X₂) S.f) := hl.mono_f
  have he : cochainTensorMap S.f (𝟙 S.X₁) ≫ cochainTensorMap (𝟙 S.X₂) S.f =
      tensorSquareMap S.f := by
    rw [cochainTensorMap_comp, comp_id, id_comp]
  rw [← he]
  infer_instance

lemma tensorSquareKernelFirstMap_mono
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (hproj : ∀ i, Module.Projective R (S.X₃.X i)) : Mono (tensorSquareKernelFirstMap S) := by
  have := tensorSquareMap_mono_of_shortExact S hS hproj
  exact mono_of_mono_fac (tensorSquareKernelFirstMap_inclusion S)

@[reassoc]
lemma tensorSquareKernelFirstMap_swap
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) :
    tensorSquareKernelFirstMap S ≫ tensorSquareKernelSwap S.g =
      tensorSquareSwap S.X₁ ≫ tensorSquareKernelFirstMap S := by
  apply (cancel_mono (tensorSquareKernelInclusion S.g)).1
  simp only [Category.assoc, tensorSquareKernelSwap_inclusion,
    tensorSquareKernelFirstMap_inclusion_assoc, tensorSquareKernelFirstMap_inclusion]
  exact tensorSquareSwap_naturality S.f

end Adams
end SerrePositivity
