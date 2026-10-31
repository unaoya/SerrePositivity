module

public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import SerrePositivity.HomologicalAlgebra.CochainTensor.DegreeMaps
public import SerrePositivity.PerfectComplex.Tensor.Perfect
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Cone
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import SerrePositivity.HomologicalAlgebra.CochainTensor.ShortExact
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Shuffle
public import SerrePositivity.PerfectComplex.Perfect.HomotopyCategory
public import SerrePositivity.KTheory.Adams.TensorCubeEigenspaces

/-! # The outer layer of the tensor-cube filtration -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
namespace Adams
variable {R : Type u} [CommRing R]
variable {P D : CochainComplex (ModuleCat.{u} R) ℤ}

abbrev tensorCubeKernel (q : P ⟶ D) := kernel (tensorCubeMap q)
abbrev tensorCubeKernelInclusion (q : P ⟶ D) : tensorCubeKernel q ⟶ tensorCube P :=
  kernel.ι (tensorCubeMap q)

/-- Right rotation preserves the tensors with at least one kernel factor. -/
def tensorCubeKernelRotation (q : P ⟶ D) : tensorCubeKernel q ⟶ tensorCubeKernel q :=
  kernel.lift (tensorCubeMap q) (tensorCubeKernelInclusion q ≫ tensorCubeRotation P) (by
    rw [Category.assoc, ← tensorCubeRotation_naturality, ← Category.assoc,
      kernel.condition, zero_comp])

@[simp, reassoc]
lemma tensorCubeKernelRotation_inclusion (q : P ⟶ D) :
    tensorCubeKernelRotation q ≫ tensorCubeKernelInclusion q =
      tensorCubeKernelInclusion q ≫ tensorCubeRotation P := kernel.lift_ι _ _ _

lemma tensorCubeKernelRotation_cube (q : P ⟶ D) :
    tensorCubeKernelRotation q ≫ tensorCubeKernelRotation q ≫ tensorCubeKernelRotation q = 𝟙 _ := by
  apply (cancel_mono (tensorCubeKernelInclusion q)).mp
  simp only [Category.assoc, tensorCubeKernelRotation_inclusion,
    tensorCubeKernelRotation_inclusion_assoc, tensorCubeRotation_cube, comp_id, id_comp]

def tensorCubeKernelAction (q : P ⟶ D) : CochainCubicAction (tensorCubeKernel q) :=
  ⟨tensorCubeKernelRotation q, tensorCubeKernelRotation_cube q⟩

abbrev tensorCubeKernelShortComplex (q : P ⟶ D) :=
  ShortComplex.mk (tensorCubeKernelInclusion q) (tensorCubeMap q) (kernel.condition _)

lemma tensorCubeMap_epi_of_shortExact
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (hproj : ∀ i, Module.Projective R (S.X₃.X i)) : Epi (tensorCubeMap S.g) := by
  let σ := cochainDegreewiseSplittingOfProjective S hS hproj
  have h1 := cochainTensorTripleShortComplexFirst_shortExact S σ S.X₂ S.X₂
  have h2 := cochainTensorTripleShortComplexSecond_shortExact S.X₃ S σ S.X₂
  have h3 := cochainTensorTripleShortComplexThird_shortExact S.X₃ S.X₃ S σ
  have : Epi (cochainTensorMap (cochainTensorMap S.g (𝟙 S.X₂)) (𝟙 S.X₂)) := h1.epi_g
  have : Epi (cochainTensorMap (cochainTensorMap (𝟙 S.X₃) S.g) (𝟙 S.X₂)) := h2.epi_g
  have : Epi (cochainTensorMap (𝟙 (cochainTensor S.X₃ S.X₃)) S.g) := h3.epi_g
  have he : cochainTensorMap (cochainTensorMap S.g (𝟙 S.X₂)) (𝟙 S.X₂) ≫
      cochainTensorMap (cochainTensorMap (𝟙 S.X₃) S.g) (𝟙 S.X₂) ≫
      cochainTensorMap (𝟙 (cochainTensor S.X₃ S.X₃)) S.g = tensorCubeMap S.g := by
    simp only [cochainTensorMap_comp, comp_id, id_comp]
  rw [← he]
  infer_instance

lemma tensorCubeKernelShortComplex_shortExact
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (hproj : ∀ i, Module.Projective R (S.X₃.X i)) :
    (tensorCubeKernelShortComplex S.g).ShortExact := by
  have := tensorCubeMap_epi_of_shortExact S hS hproj
  exact { exact := ShortComplex.exact_kernel (tensorCubeMap S.g) }

lemma tensorCubeKernel_perfect
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (hp : strictlyPerfectComplex R S.X₂) (hd : strictlyPerfectComplex R S.X₃) :
    strictlyPerfectComplex R (tensorCubeKernel S.g) :=
  strictlyPerfectComplex_of_shortExact (tensorCubeKernelShortComplex S.g)
    (tensorCubeKernelShortComplex_shortExact S hS (fun i => (hd.2 i).2))
    (tensorCube_perfect S.X₂ hp) (fun i => ((tensorCube_perfect S.X₃ hd).2 i).2)

lemma tensorCubeKernel_support {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (hp : strictlyPerfectComplex R S.X₂) (hd : strictlyPerfectComplex R S.X₃)
    (hsP : HasHomologySupportOn Z S.X₂) (hsD : HasHomologySupportOn Z S.X₃) :
    HasHomologySupportOn Z (tensorCubeKernel S.g) :=
  HasHomologySupportOn.of_shortExact (tensorCubeKernelShortComplex S.g)
    (tensorCubeKernelShortComplex_shortExact S hS (fun i => (hd.2 i).2))
    (tensorCube_support hp hsP) (tensorCube_support hd hsD)

/-- The first filtration piece embeds by tensoring the original inclusion three times. -/
def tensorCubeKernelFirstMap (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) :
    tensorCube S.X₁ ⟶ tensorCubeKernel S.g :=
  kernel.lift (tensorCubeMap S.g) (tensorCubeMap S.f) (by
    rw [← tensorCubeMap_comp, S.zero]
    simp only [tensorCubeMap, cochainTensorTripleMap, cochainTensorMap_zero_left])

@[simp, reassoc]
lemma tensorCubeKernelFirstMap_inclusion
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) :
    tensorCubeKernelFirstMap S ≫ tensorCubeKernelInclusion S.g = tensorCubeMap S.f :=
  kernel.lift_ι _ _ _

lemma tensorCubeMap_mono_of_shortExact
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (hproj : ∀ i, Module.Projective R (S.X₃.X i)) : Mono (tensorCubeMap S.f) := by
  let σ := cochainDegreewiseSplittingOfProjective S hS hproj
  have h1 := cochainTensorTripleShortComplexFirst_shortExact S σ S.X₁ S.X₁
  have h2 := cochainTensorTripleShortComplexSecond_shortExact S.X₂ S σ S.X₁
  have h3 := cochainTensorTripleShortComplexThird_shortExact S.X₂ S.X₂ S σ
  have : Mono (cochainTensorMap (cochainTensorMap S.f (𝟙 S.X₁)) (𝟙 S.X₁)) := h1.mono_f
  have : Mono (cochainTensorMap (cochainTensorMap (𝟙 S.X₂) S.f) (𝟙 S.X₁)) := h2.mono_f
  have : Mono (cochainTensorMap (𝟙 (cochainTensor S.X₂ S.X₂)) S.f) := h3.mono_f
  have he : cochainTensorMap (cochainTensorMap S.f (𝟙 S.X₁)) (𝟙 S.X₁) ≫
      cochainTensorMap (cochainTensorMap (𝟙 S.X₂) S.f) (𝟙 S.X₁) ≫
      cochainTensorMap (𝟙 (cochainTensor S.X₂ S.X₂)) S.f = tensorCubeMap S.f := by
    simp only [cochainTensorMap_comp, comp_id, id_comp]
  rw [← he]
  infer_instance

lemma tensorCubeKernelFirstMap_mono
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (hproj : ∀ i, Module.Projective R (S.X₃.X i)) : Mono (tensorCubeKernelFirstMap S) := by
  have := tensorCubeMap_mono_of_shortExact S hS hproj
  exact mono_of_mono_fac (tensorCubeKernelFirstMap_inclusion S)

@[reassoc]
lemma tensorCubeKernelFirstMap_rotation
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) :
    tensorCubeKernelFirstMap S ≫ tensorCubeKernelRotation S.g =
      tensorCubeRotation S.X₁ ≫ tensorCubeKernelFirstMap S := by
  apply (cancel_mono (tensorCubeKernelInclusion S.g)).mp
  simp only [Category.assoc, tensorCubeKernelRotation_inclusion,
    tensorCubeKernelFirstMap_inclusion_assoc, tensorCubeKernelFirstMap_inclusion]
  exact tensorCubeRotation_naturality S.f

end Adams
end SerrePositivity
