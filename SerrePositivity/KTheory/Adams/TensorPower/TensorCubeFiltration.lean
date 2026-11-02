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
public import SerrePositivity.KTheory.Adams.TensorPower.TensorCube
public import SerrePositivity.PerfectComplex.Eigen.Idempotent
public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import SerrePositivity.HomologicalAlgebra.Complex.Idempotent

/-! # テンソル三乗のフィルトレーション

## 概要

短完全列のテンソル三乗のフィルトレーションの外側の層と、不変な最初の中間の核、その四つの低次の成分、最初の層の疎な再構成を与える。

## 方針

因子の選び方で添字づけた成分に分け、巡回作用で移り合うものをまとめる。

## 規約

三乗の分割は D → E → {F, G} → H の順（refactor-plan §6.4.1）。

## 使われ方

`TensorPower/TensorCubeLowMixed`・`TensorCubeHighMixed`。
-/

@[expose] public noncomputable section

universe u

section TensorCubeFiltrationPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
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

end TensorCubeFiltrationPart

section TensorCubeFirstLayerPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
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

@[reassoc]
lemma tensorCubeFirstLayerFirstMap_rotation
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) :
    tensorCubeFirstLayerFirstMap S ≫ tensorCubeFirstLayerRotation S.g =
      tensorCubeRotation S.X₁ ≫ tensorCubeFirstLayerFirstMap S := by
  apply (cancel_mono (tensorCubeFirstLayerInclusion S.g)).mp
  simp only [Category.assoc, tensorCubeFirstLayerRotation_inclusion,
    tensorCubeFirstLayerFirstMap_inclusion_assoc, tensorCubeFirstLayerFirstMap_inclusion]
  exact tensorCubeRotation_naturality S.f

end Adams
end SerrePositivity

end TensorCubeFirstLayerPart

section TensorCubeFirstLayerSplittingPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
namespace Adams
variable {R : Type u} [CommRing R]
variable {P D : CochainComplex (ModuleCat.{u} R) ℤ}

/-- Keep the four graded components containing at most one quotient factor. -/
def tensorCubeLowDegreeMap (a b : ∀ i, P.X i ⟶ P.X i) (n : ℤ) :
    (tensorCube P).X n ⟶ (tensorCube P).X n :=
  cochainTensorTripleDegreeMap a a a n + cochainTensorTripleDegreeMap b a a n +
    cochainTensorTripleDegreeMap a b a n + cochainTensorTripleDegreeMap a a b n

lemma tensorCubeLowDegreeMap_pair0 (q : P ⟶ D) (a b : ∀ i, P.X i ⟶ P.X i)
    (ha : (fun i => a i ≫ q.f i) = (fun i => (0 : P.X i ⟶ D.X i))) (n : ℤ) :
    tensorCubeLowDegreeMap a b n ≫ (tensorCubePairMap0 q).f n = 0 := by
  rw [← cochainTensorTripleDegreeMap_eq q q (𝟙 P) n]
  simp only [tensorCubeLowDegreeMap, add_comp, cochainTensorTripleDegreeMap_comp, ha,
    cochainTensorTripleDegreeMap_zero_first, cochainTensorTripleDegreeMap_zero_second,
    add_zero]

lemma tensorCubeLowDegreeMap_pair1 (q : P ⟶ D) (a b : ∀ i, P.X i ⟶ P.X i)
    (ha : (fun i => a i ≫ q.f i) = (fun i => (0 : P.X i ⟶ D.X i))) (n : ℤ) :
    tensorCubeLowDegreeMap a b n ≫ (tensorCubePairMap1 q).f n = 0 := by
  rw [← cochainTensorTripleDegreeMap_eq (𝟙 P) q q n]
  simp only [tensorCubeLowDegreeMap, add_comp, cochainTensorTripleDegreeMap_comp, ha,
    cochainTensorTripleDegreeMap_zero_second, cochainTensorTripleDegreeMap_zero_third,
    add_zero]

lemma tensorCubeLowDegreeMap_pair2 (q : P ⟶ D) (a b : ∀ i, P.X i ⟶ P.X i)
    (ha : (fun i => a i ≫ q.f i) = (fun i => (0 : P.X i ⟶ D.X i))) (n : ℤ) :
    tensorCubeLowDegreeMap a b n ≫ (tensorCubePairMap2 q).f n = 0 := by
  rw [← cochainTensorTripleDegreeMap_eq q (𝟙 P) q n]
  simp only [tensorCubeLowDegreeMap, add_comp, cochainTensorTripleDegreeMap_comp, ha,
    cochainTensorTripleDegreeMap_zero_first, cochainTensorTripleDegreeMap_zero_third,
    add_zero]

lemma tensorCubeLowDegreeMap_pairMap (q : P ⟶ D) (a b : ∀ i, P.X i ⟶ P.X i)
    (ha : (fun i => a i ≫ q.f i) = (fun i => (0 : P.X i ⟶ D.X i))) (n : ℤ) :
    tensorCubeLowDegreeMap a b n ≫ (tensorCubePairMap q).f n = 0 := by
  apply cochainBiprodDegree_hom_ext
    (cochainTensor (cochainTensor D D) P)
    (cochainTensor (cochainTensor P D) D ⊞ cochainTensor (cochainTensor D P) D) n
  · rw [Category.assoc, ← HomologicalComplex.comp_f, tensorCubePairMap, biprod.lift_fst]
    simpa only [zero_comp] using tensorCubeLowDegreeMap_pair0 q a b ha n
  · apply cochainBiprodDegree_hom_ext (cochainTensor (cochainTensor P D) D)
      (cochainTensor (cochainTensor D P) D) n
    · rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f,
        ← HomologicalComplex.comp_f, tensorCubePairMap, biprod.lift_snd_assoc, biprod.lift_fst]
      simpa only [zero_comp] using tensorCubeLowDegreeMap_pair1 q a b ha n
    · rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f,
        ← HomologicalComplex.comp_f, tensorCubePairMap, biprod.lift_snd_assoc, biprod.lift_snd]
      simpa only [zero_comp] using tensorCubeLowDegreeMap_pair2 q a b ha n

lemma tensorCubeFirstLayerInclusion_bbc_zero (q : P ⟶ D)
    (s : ∀ i, D.X i ⟶ P.X i) (c : ∀ i, P.X i ⟶ P.X i) (n : ℤ) :
    (tensorCubeFirstLayerInclusion q).f n ≫
      cochainTensorTripleDegreeMap (fun i => q.f i ≫ s i) (fun i => q.f i ≫ s i) c n = 0 := by
  have he : (tensorCubePairMap0 q).f n ≫ cochainTensorTripleDegreeMap s s c n =
      cochainTensorTripleDegreeMap (fun i => q.f i ≫ s i) (fun i => q.f i ≫ s i) c n := by
    rw [← cochainTensorTripleDegreeMap_eq q q (𝟙 P) n, cochainTensorTripleDegreeMap_comp]
    simp only [HomologicalComplex.id_f, id_comp]
  rw [← he, ← Category.assoc, ← HomologicalComplex.comp_f,
    tensorCubeFirstLayerInclusion_pair0, HomologicalComplex.zero_f, zero_comp]

lemma tensorCubeFirstLayerInclusion_bcb_zero (q : P ⟶ D)
    (s : ∀ i, D.X i ⟶ P.X i) (c : ∀ i, P.X i ⟶ P.X i) (n : ℤ) :
    (tensorCubeFirstLayerInclusion q).f n ≫
      cochainTensorTripleDegreeMap (fun i => q.f i ≫ s i) c (fun i => q.f i ≫ s i) n = 0 := by
  have he : (tensorCubePairMap2 q).f n ≫ cochainTensorTripleDegreeMap s c s n =
      cochainTensorTripleDegreeMap (fun i => q.f i ≫ s i) c (fun i => q.f i ≫ s i) n := by
    rw [← cochainTensorTripleDegreeMap_eq q (𝟙 P) q n, cochainTensorTripleDegreeMap_comp]
    simp only [HomologicalComplex.id_f, id_comp]
  rw [← he, ← Category.assoc, ← HomologicalComplex.comp_f,
    tensorCubeFirstLayerInclusion_pair2, HomologicalComplex.zero_f, zero_comp]

lemma tensorCubeFirstLayerInclusion_cbb_zero (q : P ⟶ D)
    (s : ∀ i, D.X i ⟶ P.X i) (c : ∀ i, P.X i ⟶ P.X i) (n : ℤ) :
    (tensorCubeFirstLayerInclusion q).f n ≫
      cochainTensorTripleDegreeMap c (fun i => q.f i ≫ s i) (fun i => q.f i ≫ s i) n = 0 := by
  have he : (tensorCubePairMap1 q).f n ≫ cochainTensorTripleDegreeMap c s s n =
      cochainTensorTripleDegreeMap c (fun i => q.f i ≫ s i) (fun i => q.f i ≫ s i) n := by
    rw [← cochainTensorTripleDegreeMap_eq (𝟙 P) q q n, cochainTensorTripleDegreeMap_comp]
    simp only [HomologicalComplex.id_f, id_comp]
  rw [← he, ← Category.assoc, ← HomologicalComplex.comp_f,
    tensorCubeFirstLayerInclusion_pair1, HomologicalComplex.zero_f, zero_comp]

/-- On the common kernel the four low components reconstruct the inclusion. -/
lemma tensorCubeFirstLayerInclusion_low (q : P ⟶ D) (a : ∀ i, P.X i ⟶ P.X i)
    (s : ∀ i, D.X i ⟶ P.X i)
    (hp : (fun i => a i + q.f i ≫ s i) = (fun i => 𝟙 (P.X i))) (n : ℤ) :
    (tensorCubeFirstLayerInclusion q).f n ≫
      tensorCubeLowDegreeMap a (fun i => q.f i ≫ s i) n =
        (tensorCubeFirstLayerInclusion q).f n := by
  let b := fun i => q.f i ≫ s i
  have he := congrArg (fun v => (tensorCubeFirstLayerInclusion q).f n ≫ v)
    (cochainTensorTripleDegreeMap_partition a b hp n)
  simp only [b, comp_add, comp_id, tensorCubeFirstLayerInclusion_bbc_zero,
    tensorCubeFirstLayerInclusion_bcb_zero, tensorCubeFirstLayerInclusion_cbb_zero,
    add_zero] at he
  rw [tensorCubeLowDegreeMap, comp_add, comp_add, comp_add]
  exact he

variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting)

abbrev tensorCubeSplittingA (i : ℤ) : S.X₂.X i ⟶ S.X₂.X i :=
  cochainSplittingRetraction S σ i ≫ S.f.f i
abbrev tensorCubeSplittingB (i : ℤ) : S.X₂.X i ⟶ S.X₂.X i :=
  S.g.f i ≫ cochainSplittingSection S σ i

lemma tensorCubeSplittingA_quotient_zero :
    (fun i => tensorCubeSplittingA S σ i ≫ S.g.f i) =
      (fun i => (0 : S.X₂.X i ⟶ S.X₃.X i)) := by
  funext i
  rw [tensorCubeSplittingA, Category.assoc, ← HomologicalComplex.comp_f,
    S.zero, HomologicalComplex.zero_f, comp_zero]

/-- The graded four-component projection lifted into the common kernel. -/
def tensorCubeFirstLayerRetractionX (n : ℤ) :
    (tensorCube S.X₂).X n ⟶ (tensorCubeFirstLayer S.g).X n :=
  cochainKernelLiftX (tensorCubePairMap S.g) n
    (tensorCubeLowDegreeMap (tensorCubeSplittingA S σ) (tensorCubeSplittingB S σ) n)
    (tensorCubeLowDegreeMap_pairMap S.g _ _ (tensorCubeSplittingA_quotient_zero S σ) n)

@[reassoc]
lemma tensorCubeFirstLayerRetractionX_inclusion (n : ℤ) :
    tensorCubeFirstLayerRetractionX S σ n ≫ (tensorCubeFirstLayerInclusion S.g).f n =
      tensorCubeLowDegreeMap (tensorCubeSplittingA S σ) (tensorCubeSplittingB S σ) n :=
  cochainKernelLiftX_inclusion _ _ _ _

lemma tensorCubeFirstLayerRetractionX_retract (n : ℤ) :
    (tensorCubeFirstLayerInclusion S.g).f n ≫ tensorCubeFirstLayerRetractionX S σ n = 𝟙 _ := by
  apply (cancel_mono ((tensorCubeFirstLayerInclusion S.g).f n)).mp
  rw [Category.assoc, tensorCubeFirstLayerRetractionX_inclusion, id_comp]
  exact tensorCubeFirstLayerInclusion_low S.g _ (cochainSplittingSection S σ)
    (funext fun i => (σ i).id) n

lemma tensorCubeFirstLayer_perfect (hS : S.ShortExact)
    (hp : strictlyPerfectComplex R S.X₂) (hd : strictlyPerfectComplex R S.X₃) :
    strictlyPerfectComplex R (tensorCubeFirstLayer S.g) := by
  let σ := cochainDegreewiseSplittingOfProjective S hS (fun i => (hd.2 i).2)
  exact strictlyPerfectComplex_of_degreewiseRetract (tensorCubeFirstLayerInclusion S.g)
    (tensorCubeFirstLayerRetractionX S σ) (tensorCubeFirstLayerRetractionX_retract S σ)
    (tensorCube_perfect S.X₂ hp)

end Adams
end SerrePositivity

end TensorCubeFirstLayerSplittingPart

section TensorCubeSparsePartitionPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
variable {R : Type u} [CommRing R]

namespace Adams
variable {P D : CochainComplex (ModuleCat.{u} R) ℤ}

lemma tensorCubeFirstLayerInclusion_sparse (q : P ⟶ D)
    (a : ∀ i, P.X i ⟶ P.X i) (s : ∀ i, D.X i ⟶ P.X i)
    (hp : (fun i => a i + q.f i ≫ s i) = (fun i => 𝟙 (P.X i))) (n : ℤ) :
    (tensorCubeFirstLayerInclusion q).f n ≫ cochainTensorTripleDegreeMap a a a n +
      (tensorCubeFirstLayerInclusion q).f n ≫ cochainTensorTripleDegreeMap
        (fun i => q.f i ≫ s i) (fun i => 𝟙 (P.X i)) (fun i => 𝟙 (P.X i)) n +
      (tensorCubeFirstLayerInclusion q).f n ≫ cochainTensorTripleDegreeMap
        (fun i => 𝟙 (P.X i)) (fun i => q.f i ≫ s i) (fun i => 𝟙 (P.X i)) n +
      (tensorCubeFirstLayerInclusion q).f n ≫ cochainTensorTripleDegreeMap
        (fun i => 𝟙 (P.X i)) (fun i => 𝟙 (P.X i)) (fun i => q.f i ≫ s i) n =
        (tensorCubeFirstLayerInclusion q).f n := by
  have he := congrArg (fun v => (tensorCubeFirstLayerInclusion q).f n ≫ v)
    (cochainTensorTripleDegreeMap_sparse_partition a (fun i => q.f i ≫ s i) hp n)
  simp only [comp_add, comp_id, tensorCubeFirstLayerInclusion_bbc_zero,
    tensorCubeFirstLayerInclusion_bcb_zero, tensorCubeFirstLayerInclusion_cbb_zero, add_zero] at he
  exact he

end Adams
end SerrePositivity

end TensorCubeSparsePartitionPart
