module

public import SerrePositivity.KTheory.Adams.TensorCubeFiltration

/-! # The invariant first intermediate kernel in the tensor-cube filtration -/

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

abbrev tensorCubePairMap0 (q : P ⟶ D) := cochainTensorTripleMap q q (𝟙 P)
abbrev tensorCubePairMap1 (q : P ⟶ D) := cochainTensorTripleMap (𝟙 P) q q
abbrev tensorCubePairMap2 (q : P ⟶ D) := cochainTensorTripleMap q (𝟙 P) q

/-- Simultaneously extract the DDP, PDD, and DPD parts. -/
def tensorCubePairMap (q : P ⟶ D) : tensorCube P ⟶
    cochainTensor (cochainTensor D D) P ⊞
      (cochainTensor (cochainTensor P D) D ⊞ cochainTensor (cochainTensor D P) D) :=
  biprod.lift (tensorCubePairMap0 q) (biprod.lift (tensorCubePairMap1 q) (tensorCubePairMap2 q))

abbrev tensorCubeFirstLayer (q : P ⟶ D) := kernel (tensorCubePairMap q)
abbrev tensorCubeFirstLayerInclusion (q : P ⟶ D) : tensorCubeFirstLayer q ⟶ tensorCube P :=
  kernel.ι (tensorCubePairMap q)

@[simp, reassoc]
lemma tensorCubeFirstLayerInclusion_pair0 (q : P ⟶ D) :
    tensorCubeFirstLayerInclusion q ≫ tensorCubePairMap0 q = 0 := by
  have he := (kernel.condition (tensorCubePairMap q)) =≫ biprod.fst
  simp only [tensorCubePairMap, Category.assoc, biprod.lift_fst, zero_comp] at he
  exact he

@[simp, reassoc]
lemma tensorCubeFirstLayerInclusion_pair1 (q : P ⟶ D) :
    tensorCubeFirstLayerInclusion q ≫ tensorCubePairMap1 q = 0 := by
  have he := (kernel.condition (tensorCubePairMap q)) =≫ (biprod.snd ≫ biprod.fst)
  simp only [tensorCubePairMap, Category.assoc, biprod.lift_snd_assoc, biprod.lift_fst,
    zero_comp] at he
  exact he

@[simp, reassoc]
lemma tensorCubeFirstLayerInclusion_pair2 (q : P ⟶ D) :
    tensorCubeFirstLayerInclusion q ≫ tensorCubePairMap2 q = 0 := by
  have he := (kernel.condition (tensorCubePairMap q)) =≫ (biprod.snd ≫ biprod.snd)
  simp only [tensorCubePairMap, Category.assoc, biprod.lift_snd_assoc, biprod.lift_snd,
    zero_comp] at he
  exact he

lemma tensorCubeRotation_pair0 (q : P ⟶ D) :
    tensorCubeRotation P ≫ tensorCubePairMap0 q =
      tensorCubePairMap2 q ≫ (cochainTensorRotationIso D P D).hom :=
  (cochainTensorRotation_naturality q (𝟙 P) q).symm

lemma tensorCubeRotation_pair1 (q : P ⟶ D) :
    tensorCubeRotation P ≫ tensorCubePairMap1 q =
      tensorCubePairMap0 q ≫ (cochainTensorRotationIso D D P).hom :=
  (cochainTensorRotation_naturality q q (𝟙 P)).symm

lemma tensorCubeRotation_pair2 (q : P ⟶ D) :
    tensorCubeRotation P ≫ tensorCubePairMap2 q =
      tensorCubePairMap1 q ≫ (cochainTensorRotationIso P D D).hom :=
  (cochainTensorRotation_naturality (𝟙 P) q q).symm

/-- Rotation restricts to the common kernel of the three pair quotient maps. -/
def tensorCubeFirstLayerRotation (q : P ⟶ D) : tensorCubeFirstLayer q ⟶ tensorCubeFirstLayer q :=
  kernel.lift (tensorCubePairMap q) (tensorCubeFirstLayerInclusion q ≫ tensorCubeRotation P) (by
    apply biprod.hom_ext
    · simp only [Category.assoc, tensorCubePairMap, biprod.lift_fst, zero_comp]
      rw [tensorCubeRotation_pair0, ← Category.assoc,
        tensorCubeFirstLayerInclusion_pair2, zero_comp]
    · apply biprod.hom_ext
      · simp only [Category.assoc, tensorCubePairMap, biprod.lift_snd_assoc,
          biprod.lift_fst, zero_comp]
        rw [tensorCubeRotation_pair1, ← Category.assoc,
          tensorCubeFirstLayerInclusion_pair0, zero_comp]
      · simp only [Category.assoc, tensorCubePairMap, biprod.lift_snd, zero_comp]
        rw [tensorCubeRotation_pair2, ← Category.assoc,
          tensorCubeFirstLayerInclusion_pair1, zero_comp])

@[simp, reassoc]
lemma tensorCubeFirstLayerRotation_inclusion (q : P ⟶ D) :
    tensorCubeFirstLayerRotation q ≫ tensorCubeFirstLayerInclusion q =
      tensorCubeFirstLayerInclusion q ≫ tensorCubeRotation P := kernel.lift_ι _ _ _

lemma tensorCubeFirstLayerRotation_cube (q : P ⟶ D) :
    tensorCubeFirstLayerRotation q ≫ tensorCubeFirstLayerRotation q ≫
      tensorCubeFirstLayerRotation q = 𝟙 _ := by
  apply (cancel_mono (tensorCubeFirstLayerInclusion q)).mp
  simp only [Category.assoc, tensorCubeFirstLayerRotation_inclusion,
    tensorCubeFirstLayerRotation_inclusion_assoc, tensorCubeRotation_cube, comp_id, id_comp]

def tensorCubeFirstLayerAction (q : P ⟶ D) : CochainCubicAction (tensorCubeFirstLayer q) :=
  ⟨tensorCubeFirstLayerRotation q, tensorCubeFirstLayerRotation_cube q⟩

/-- Vanishing of the pair quotient maps forces vanishing of the triple quotient map. -/
lemma tensorCubeFirstLayerInclusion_cubeMap (q : P ⟶ D) :
    tensorCubeFirstLayerInclusion q ≫ tensorCubeMap q = 0 := by
  have he : tensorCubePairMap0 q ≫ cochainTensorMap (𝟙 (cochainTensor D D)) q =
      tensorCubeMap q := by simp only [cochainTensorMap_comp, comp_id, id_comp]
  rw [← he, ← Category.assoc, tensorCubeFirstLayerInclusion_pair0, zero_comp]

/-- The first intermediate kernel embeds in the outer kernel. -/
def tensorCubeFirstLayerToKernel (q : P ⟶ D) : tensorCubeFirstLayer q ⟶ tensorCubeKernel q :=
  kernel.lift (tensorCubeMap q) (tensorCubeFirstLayerInclusion q)
    (tensorCubeFirstLayerInclusion_cubeMap q)

@[simp, reassoc]
lemma tensorCubeFirstLayerToKernel_inclusion (q : P ⟶ D) :
    tensorCubeFirstLayerToKernel q ≫ tensorCubeKernelInclusion q =
      tensorCubeFirstLayerInclusion q := kernel.lift_ι _ _ _

instance tensorCubeFirstLayerToKernel_mono (q : P ⟶ D) : Mono (tensorCubeFirstLayerToKernel q) :=
  mono_of_mono_fac (tensorCubeFirstLayerToKernel_inclusion q)

@[reassoc]
lemma tensorCubeFirstLayerToKernel_rotation (q : P ⟶ D) :
    tensorCubeFirstLayerToKernel q ≫ tensorCubeKernelRotation q =
      tensorCubeFirstLayerRotation q ≫ tensorCubeFirstLayerToKernel q := by
  apply (cancel_mono (tensorCubeKernelInclusion q)).mp
  simp only [Category.assoc, tensorCubeKernelRotation_inclusion,
    tensorCubeFirstLayerToKernel_inclusion_assoc,
    tensorCubeFirstLayerToKernel_inclusion, tensorCubeFirstLayerRotation_inclusion]

/-- The triple of the first term belongs to the common pair kernel. -/
def tensorCubeFirstLayerFirstMap
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) :
    tensorCube S.X₁ ⟶ tensorCubeFirstLayer S.g :=
  kernel.lift (tensorCubePairMap S.g) (tensorCubeMap S.f) (by
    apply biprod.hom_ext
    · simp only [Category.assoc, tensorCubePairMap, biprod.lift_fst, zero_comp]
      simp only [tensorCubeMap, tensorCubePairMap0, cochainTensorTripleMap,
        cochainTensorMap_comp, S.zero, comp_id, cochainTensorMap_zero_left]
    · apply biprod.hom_ext
      · simp only [Category.assoc, tensorCubePairMap, biprod.lift_snd_assoc,
          biprod.lift_fst, zero_comp]
        simp only [tensorCubeMap, tensorCubePairMap1, cochainTensorTripleMap,
          cochainTensorMap_comp, S.zero, comp_id, cochainTensorMap_zero_right]
      · simp only [Category.assoc, tensorCubePairMap, biprod.lift_snd, zero_comp]
        simp only [tensorCubeMap, tensorCubePairMap2, cochainTensorTripleMap,
          cochainTensorMap_comp, S.zero, comp_id, cochainTensorMap_zero_left])

@[simp, reassoc]
lemma tensorCubeFirstLayerFirstMap_inclusion
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) :
    tensorCubeFirstLayerFirstMap S ≫ tensorCubeFirstLayerInclusion S.g = tensorCubeMap S.f :=
  kernel.lift_ι _ _ _

lemma tensorCubeFirstLayerFirstMap_mono
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (hproj : ∀ i, Module.Projective R (S.X₃.X i)) : Mono (tensorCubeFirstLayerFirstMap S) := by
  have := tensorCubeMap_mono_of_shortExact S hS hproj
  exact mono_of_mono_fac (tensorCubeFirstLayerFirstMap_inclusion S)

@[reassoc]
lemma tensorCubeFirstLayerFirstMap_rotation
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) :
    tensorCubeFirstLayerFirstMap S ≫ tensorCubeFirstLayerRotation S.g =
      tensorCubeRotation S.X₁ ≫ tensorCubeFirstLayerFirstMap S := by
  apply (cancel_mono (tensorCubeFirstLayerInclusion S.g)).mp
  simp only [Category.assoc, tensorCubeFirstLayerRotation_inclusion,
    tensorCubeFirstLayerFirstMap_inclusion_assoc, tensorCubeFirstLayerFirstMap_inclusion]
  exact tensorCubeRotation_naturality S.f

lemma tensorCubeFirstLayerFirstMap_toKernel
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) :
    tensorCubeFirstLayerFirstMap S ≫ tensorCubeFirstLayerToKernel S.g =
      tensorCubeKernelFirstMap S := by
  apply (cancel_mono (tensorCubeKernelInclusion S.g)).mp
  simp only [Category.assoc, tensorCubeFirstLayerToKernel_inclusion,
    tensorCubeFirstLayerFirstMap_inclusion, tensorCubeKernelFirstMap_inclusion]

end Adams
end SerrePositivity
