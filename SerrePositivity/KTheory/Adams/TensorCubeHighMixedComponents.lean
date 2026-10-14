module

public import SerrePositivity.KTheory.Adams.TensorCubeHighMixed
public import SerrePositivity.PerfectComplex.TensorTripleCyclicSum

/-! # The three high mixed tensor-cube components and their inclusions -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits
namespace Adams
private lemma high_comp_twice_natural {C : Type*} [Category C] {K P : C}
    (r : K ⟶ K) (i : K ⟶ P) (t : P ⟶ P) (h : r ≫ i = i ≫ t) :
    r ≫ r ≫ i = i ≫ t ≫ t := by
  calc
    _ = r ≫ i ≫ t := r ≫= h
    _ = _ := by simpa only [Category.assoc] using h =≫ t

variable {R : Type u} [CommRing R]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (hS : S.ShortExact) (hproj : ∀ i, Module.Projective R (S.X₃.X i))

def tensorCubeHighMixed1 : tensorCubeKernel S.g ⟶
    cochainTensor (cochainTensor S.X₁ S.X₃) S.X₃ :=
  tensorCubeKernelRotation S.g ≫ tensorCubeKernelRotation S.g ≫
    tensorCubeHighMixed0 S hS hproj ≫ (cochainTensorRotationIso S.X₃ S.X₃ S.X₁).hom

def tensorCubeHighMixed2 : tensorCubeKernel S.g ⟶
    cochainTensor (cochainTensor S.X₃ S.X₁) S.X₃ :=
  tensorCubeKernelRotation S.g ≫ tensorCubeHighMixed0 S hS hproj ≫
    (cochainTensorRotationIso S.X₃ S.X₃ S.X₁).hom ≫
    (cochainTensorRotationIso S.X₁ S.X₃ S.X₃).hom

@[reassoc]
lemma tensorCubeKernelRotation_highMixed0 :
    tensorCubeKernelRotation S.g ≫ tensorCubeHighMixed0 S hS hproj =
      tensorCubeHighMixed2 S hS hproj ≫ (cochainTensorRotationIso S.X₃ S.X₁ S.X₃).hom := by
  simp only [tensorCubeHighMixed2, Category.assoc, cochainTensorRotation_cube, comp_id]

@[reassoc]
lemma tensorCubeKernelRotation_highMixed1 :
    tensorCubeKernelRotation S.g ≫ tensorCubeHighMixed1 S hS hproj =
      tensorCubeHighMixed0 S hS hproj ≫ (cochainTensorRotationIso S.X₃ S.X₃ S.X₁).hom := by
  simpa only [tensorCubeHighMixed1, Category.assoc, id_comp] using
    (tensorCubeKernelRotation_cube S.g) =≫
      (tensorCubeHighMixed0 S hS hproj ≫ (cochainTensorRotationIso S.X₃ S.X₃ S.X₁).hom)

@[reassoc]
lemma tensorCubeKernelRotation_highMixed2 :
    tensorCubeKernelRotation S.g ≫ tensorCubeHighMixed2 S hS hproj =
      tensorCubeHighMixed1 S hS hproj ≫ (cochainTensorRotationIso S.X₁ S.X₃ S.X₃).hom := by
  simp only [tensorCubeHighMixed1, tensorCubeHighMixed2, Category.assoc]

@[reassoc]
lemma tensorCubeHighMixed1_inclusion :
    tensorCubeHighMixed1 S hS hproj ≫ cochainTensorTripleMap S.f (𝟙 S.X₃) (𝟙 S.X₃) =
      tensorCubeKernelInclusion S.g ≫ tensorCubePairMap1 S.g := by
  simp only [tensorCubeHighMixed1, Category.assoc]
  rw [← cochainTensorRotation_naturality (𝟙 S.X₃) (𝟙 S.X₃) S.f,
    ← Category.assoc (tensorCubeHighMixed0 S hS hproj), tensorCubeHighMixed0_inclusion]
  simp only [Category.assoc]
  have hi := high_comp_twice_natural (tensorCubeKernelRotation S.g)
    (tensorCubeKernelInclusion S.g) (tensorCubeRotation S.X₂)
    (tensorCubeKernelRotation_inclusion S.g)
  have hh : tensorCubeKernelRotation S.g ≫ tensorCubeKernelRotation S.g ≫
      tensorCubeKernelInclusion S.g ≫ tensorCubePairMap0 S.g ≫
      (cochainTensorRotationIso S.X₃ S.X₃ S.X₂).hom =
      tensorCubeKernelInclusion S.g ≫ tensorCubeRotation S.X₂ ≫ tensorCubeRotation S.X₂ ≫
        tensorCubePairMap0 S.g ≫ (cochainTensorRotationIso S.X₃ S.X₃ S.X₂).hom := by
    simpa only [Category.assoc] using hi =≫
      (tensorCubePairMap0 S.g ≫ (cochainTensorRotationIso S.X₃ S.X₃ S.X₂).hom)
  refine hh.trans ?_
  rw [tensorCubePairMap0, cochainTensorRotation_naturality S.g S.g (𝟙 S.X₂)]
  simpa only [Category.assoc, id_comp] using tensorCubeKernelInclusion S.g ≫=
    ((tensorCubeRotation_cube S.X₂) =≫ tensorCubePairMap1 S.g)

@[reassoc]
lemma tensorCubeHighMixed2_inclusion :
    tensorCubeHighMixed2 S hS hproj ≫ cochainTensorTripleMap (𝟙 S.X₃) S.f (𝟙 S.X₃) =
      tensorCubeKernelInclusion S.g ≫ tensorCubePairMap2 S.g := by
  simp only [tensorCubeHighMixed2, Category.assoc]
  rw [← cochainTensorRotation_naturality S.f (𝟙 S.X₃) (𝟙 S.X₃),
    ← cochainTensorRotation_naturality_assoc (𝟙 S.X₃) (𝟙 S.X₃) S.f,
    ← Category.assoc (tensorCubeHighMixed0 S hS hproj), tensorCubeHighMixed0_inclusion]
  simp only [Category.assoc]
  have hi := tensorCubeKernelRotation_inclusion S.g
  have hh : tensorCubeKernelRotation S.g ≫ tensorCubeKernelInclusion S.g ≫
      tensorCubePairMap0 S.g ≫ (cochainTensorRotationIso S.X₃ S.X₃ S.X₂).hom ≫
      (cochainTensorRotationIso S.X₂ S.X₃ S.X₃).hom =
      tensorCubeKernelInclusion S.g ≫ tensorCubeRotation S.X₂ ≫ tensorCubePairMap0 S.g ≫
        (cochainTensorRotationIso S.X₃ S.X₃ S.X₂).hom ≫
        (cochainTensorRotationIso S.X₂ S.X₃ S.X₃).hom := by
    simpa only [Category.assoc] using hi =≫
      (tensorCubePairMap0 S.g ≫ (cochainTensorRotationIso S.X₃ S.X₃ S.X₂).hom ≫
        (cochainTensorRotationIso S.X₂ S.X₃ S.X₃).hom)
  refine hh.trans ?_
  rw [tensorCubePairMap0, cochainTensorRotation_naturality_assoc S.g S.g (𝟙 S.X₂),
    cochainTensorRotation_naturality (𝟙 S.X₂) S.g S.g]
  simpa only [Category.assoc, id_comp] using tensorCubeKernelInclusion S.g ≫=
    ((tensorCubeRotation_cube S.X₂) =≫ tensorCubePairMap2 S.g)

include hS hproj in
lemma tensorCubeHighMixed1_target_inclusion_mono :
    Mono (cochainTensorTripleMap S.f (𝟙 S.X₃) (𝟙 S.X₃)) :=
  (cochainTensorTripleShortComplexFirst_shortExact S
    (cochainDegreewiseSplittingOfProjective S hS hproj) S.X₃ S.X₃).mono_f

include hS hproj in
lemma tensorCubeHighMixed2_target_inclusion_mono :
    Mono (cochainTensorTripleMap (𝟙 S.X₃) S.f (𝟙 S.X₃)) :=
  (cochainTensorTripleShortComplexSecond_shortExact S.X₃ S
    (cochainDegreewiseSplittingOfProjective S hS hproj) S.X₃).mono_f

abbrev tensorCubeHighMixedTarget := cochainTensorCyclicSum S.X₃ S.X₃ S.X₁

def tensorCubeHighMixedMap : tensorCubeKernel S.g ⟶ tensorCubeHighMixedTarget S :=
  biprod.lift (tensorCubeHighMixed0 S hS hproj)
    (biprod.lift (tensorCubeHighMixed1 S hS hproj) (tensorCubeHighMixed2 S hS hproj))

end Adams
end SerrePositivity
