module

public import SerrePositivity.KTheory.Adams.TensorPower.TensorCubeFiltration
public import SerrePositivity.PerfectComplex.Tensor.CyclicSum
public import Mathlib.CategoryTheory.CommSq
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import SerrePositivity.HomologicalAlgebra.CochainTensor.DegreeMaps
public import SerrePositivity.PerfectComplex.Tensor.Perfect
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Shuffle
public import SerrePositivity.PerfectComplex.Eigen.Idempotent
public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import SerrePositivity.HomologicalAlgebra.Complex.Idempotent
public import SerrePositivity.CategoryTheory.Triangulated.Idempotent
public import SerrePositivity.CategoryTheory.Abelian.ShortComplex

/-! # テンソル三乗の高次の混合成分

## 概要

高次の混合成分とその三つの成分・包含、次数ごとの持ち上げと切断、商写像の核の同定、台と三次の作用を持つ高次の混合商を与える。

## 方針

低次の場合と同じく、次数ごとの分裂から完全性を示す。

## 規約

余核の部分は `TensorPower/TensorCubeClass` 側で扱う。

## 使われ方

`TensorPower/TensorCubeClass`。
-/

@[expose] public noncomputable section

universe u

section TensorCubeHighMixedPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
namespace Adams
variable {R : Type u} [CommRing R]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (hS : S.ShortExact) (hproj : ∀ i, Module.Projective R (S.X₃.X i))

/-- Extract two quotient factors and lift the remaining factor into A. -/
def tensorCubeHighMixed0 : tensorCubeKernel S.g ⟶
    cochainTensor (cochainTensor S.X₃ S.X₃) S.X₁ := by
  let σ := cochainDegreewiseSplittingOfProjective S hS hproj
  have hT := cochainTensorTripleShortComplexThird_shortExact S.X₃ S.X₃ S σ
  have := hT.mono_f
  exact hT.exact.lift (tensorCubeKernelInclusion S.g ≫ tensorCubePairMap0 S.g) (by
    change (tensorCubeKernelInclusion S.g ≫ tensorCubePairMap0 S.g) ≫
      cochainTensorMap (𝟙 (cochainTensor S.X₃ S.X₃)) S.g = 0
    simp only [tensorCubePairMap0, cochainTensorTripleMap, Category.assoc,
      cochainTensorMap_comp, comp_id, id_comp]
    exact kernel.condition (tensorCubeMap S.g))

@[reassoc]
lemma tensorCubeHighMixed0_inclusion :
    tensorCubeHighMixed0 S hS hproj ≫ cochainTensorTripleMap (𝟙 S.X₃) (𝟙 S.X₃) S.f =
      tensorCubeKernelInclusion S.g ≫ tensorCubePairMap0 S.g := by
  rw [cochainTensorTripleMap, cochainTensorMap_id]
  dsimp [tensorCubeHighMixed0]
  exact Fork.IsLimit.lift_ι _

include hS hproj in
lemma tensorCubeHighMixed0_target_inclusion_mono :
    Mono (cochainTensorTripleMap (𝟙 S.X₃) (𝟙 S.X₃) S.f) := by
  rw [cochainTensorTripleMap, cochainTensorMap_id]
  exact (cochainTensorTripleShortComplexThird_shortExact S.X₃ S.X₃ S
    (cochainDegreewiseSplittingOfProjective S hS hproj)).mono_f

@[simp, reassoc]
lemma tensorCubeFirstLayerToKernel_highMixed0 :
    tensorCubeFirstLayerToKernel S.g ≫ tensorCubeHighMixed0 S hS hproj = 0 := by
  have := tensorCubeHighMixed0_target_inclusion_mono S hS hproj
  apply (cancel_mono (cochainTensorTripleMap (𝟙 S.X₃) (𝟙 S.X₃) S.f)).mp
  rw [Category.assoc, tensorCubeHighMixed0_inclusion,
    tensorCubeFirstLayerToKernel_inclusion_assoc, tensorCubeFirstLayerInclusion_pair0]
  simp only [zero_comp]

end Adams
end SerrePositivity

end TensorCubeHighMixedPart

section TensorCubeHighMixedComponentsPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits
namespace Adams
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
  have hs : CommSq (tensorCubeKernelRotation S.g) (tensorCubeKernelInclusion S.g)
      (tensorCubeKernelInclusion S.g) (tensorCubeRotation S.X₂) :=
    ⟨tensorCubeKernelRotation_inclusion S.g⟩
  have hi := (hs.horiz_comp hs).w
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

end TensorCubeHighMixedComponentsPart

section TensorCubeHighMixedSectionsPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
namespace Adams
variable {R : Type u} [CommRing R]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting)

lemma tensorCubeHighMixedSplitting_f_g :
    (fun i => S.f.f i ≫ S.g.f i) = (fun i => (0 : S.X₁.X i ⟶ S.X₃.X i)) :=
  cochainShortComplex_f_g S

/-- Lift the high mixed component 0 using two quotient sections. -/
def tensorCubeHighMixedRawSection0X (n : ℤ) :
    (cochainTensor (cochainTensor S.X₃ S.X₃) S.X₁).X n ⟶ (tensorCube S.X₂).X n :=
  cochainTensorTripleDegreeMap (cochainSplittingSection S σ) (cochainSplittingSection S σ) S.f.f n

lemma tensorCubeHighMixedRawSection0X_cubeMap_zero (n : ℤ) :
    tensorCubeHighMixedRawSection0X S σ n ≫ (tensorCubeMap S.g).f n = 0 := by
  rw [tensorCubeMap, ← cochainTensorTripleDegreeMap_eq S.g S.g S.g n]
  simp only [tensorCubeHighMixedRawSection0X, cochainTensorTripleDegreeMap_comp,
    tensorCubeHighMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_third]

def tensorCubeHighMixedSection0X (n : ℤ) :
    (cochainTensor (cochainTensor S.X₃ S.X₃) S.X₁).X n ⟶ (tensorCubeKernel S.g).X n :=
  cochainKernelLiftX (tensorCubeMap S.g) n (tensorCubeHighMixedRawSection0X S σ n)
    (tensorCubeHighMixedRawSection0X_cubeMap_zero S σ n)

@[reassoc]
lemma tensorCubeHighMixedSection0X_inclusion (n : ℤ) :
    tensorCubeHighMixedSection0X S σ n ≫ (tensorCubeKernelInclusion S.g).f n =
      tensorCubeHighMixedRawSection0X S σ n := cochainKernelLiftX_inclusion _ _ _ _

/-- Lift the high mixed component 1 using two quotient sections. -/
def tensorCubeHighMixedRawSection1X (n : ℤ) :
    (cochainTensor (cochainTensor S.X₁ S.X₃) S.X₃).X n ⟶ (tensorCube S.X₂).X n :=
  cochainTensorTripleDegreeMap S.f.f (cochainSplittingSection S σ) (cochainSplittingSection S σ) n

lemma tensorCubeHighMixedRawSection1X_cubeMap_zero (n : ℤ) :
    tensorCubeHighMixedRawSection1X S σ n ≫ (tensorCubeMap S.g).f n = 0 := by
  rw [tensorCubeMap, ← cochainTensorTripleDegreeMap_eq S.g S.g S.g n]
  simp only [tensorCubeHighMixedRawSection1X, cochainTensorTripleDegreeMap_comp,
    tensorCubeHighMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_first]

def tensorCubeHighMixedSection1X (n : ℤ) :
    (cochainTensor (cochainTensor S.X₁ S.X₃) S.X₃).X n ⟶ (tensorCubeKernel S.g).X n :=
  cochainKernelLiftX (tensorCubeMap S.g) n (tensorCubeHighMixedRawSection1X S σ n)
    (tensorCubeHighMixedRawSection1X_cubeMap_zero S σ n)

@[reassoc]
lemma tensorCubeHighMixedSection1X_inclusion (n : ℤ) :
    tensorCubeHighMixedSection1X S σ n ≫ (tensorCubeKernelInclusion S.g).f n =
      tensorCubeHighMixedRawSection1X S σ n := cochainKernelLiftX_inclusion _ _ _ _

/-- Lift the high mixed component 2 using two quotient sections. -/
def tensorCubeHighMixedRawSection2X (n : ℤ) :
    (cochainTensor (cochainTensor S.X₃ S.X₁) S.X₃).X n ⟶ (tensorCube S.X₂).X n :=
  cochainTensorTripleDegreeMap (cochainSplittingSection S σ) S.f.f (cochainSplittingSection S σ) n

lemma tensorCubeHighMixedRawSection2X_cubeMap_zero (n : ℤ) :
    tensorCubeHighMixedRawSection2X S σ n ≫ (tensorCubeMap S.g).f n = 0 := by
  rw [tensorCubeMap, ← cochainTensorTripleDegreeMap_eq S.g S.g S.g n]
  simp only [tensorCubeHighMixedRawSection2X, cochainTensorTripleDegreeMap_comp,
    tensorCubeHighMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_second]

def tensorCubeHighMixedSection2X (n : ℤ) :
    (cochainTensor (cochainTensor S.X₃ S.X₁) S.X₃).X n ⟶ (tensorCubeKernel S.g).X n :=
  cochainKernelLiftX (tensorCubeMap S.g) n (tensorCubeHighMixedRawSection2X S σ n)
    (tensorCubeHighMixedRawSection2X_cubeMap_zero S σ n)

@[reassoc]
lemma tensorCubeHighMixedSection2X_inclusion (n : ℤ) :
    tensorCubeHighMixedSection2X S σ n ≫ (tensorCubeKernelInclusion S.g).f n =
      tensorCubeHighMixedRawSection2X S σ n := cochainKernelLiftX_inclusion _ _ _ _

variable (hS : S.ShortExact) (hproj : ∀ i, Module.Projective R (S.X₃.X i))

lemma tensorCubeHighMixedSection0X_component0 (n : ℤ) :
    tensorCubeHighMixedSection0X S σ n ≫ (tensorCubeHighMixed0 S hS hproj).f n = 𝟙 _ := by
  have := tensorCubeHighMixed0_target_inclusion_mono S hS hproj
  apply cochainKernelLiftX_comp_eq (tensorCubeHighMixed0_inclusion S hS hproj)
  rw [id_comp, ← cochainTensorTripleDegreeMap_eq S.g S.g (𝟙 S.X₂) n]
  rw [tensorCubeHighMixedRawSection0X, cochainTensorTripleDegreeMap_comp]
  simp only [HomologicalComplex.id_f, comp_id]
  rw [cochainSplitting_s_g]
  exact cochainTensorTripleDegreeMap_eq (𝟙 S.X₃) (𝟙 S.X₃) S.f n

lemma tensorCubeHighMixedSection0X_component1 (n : ℤ) :
    tensorCubeHighMixedSection0X S σ n ≫ (tensorCubeHighMixed1 S hS hproj).f n = 0 := by
  have := tensorCubeHighMixed1_target_inclusion_mono S hS hproj
  apply cochainKernelLiftX_comp_eq (tensorCubeHighMixed1_inclusion S hS hproj)
  rw [← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) S.g S.g n]
  simp only [tensorCubeHighMixedRawSection0X, cochainTensorTripleDegreeMap_comp,
    tensorCubeHighMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_third, zero_comp]

lemma tensorCubeHighMixedSection0X_component2 (n : ℤ) :
    tensorCubeHighMixedSection0X S σ n ≫ (tensorCubeHighMixed2 S hS hproj).f n = 0 := by
  have := tensorCubeHighMixed2_target_inclusion_mono S hS hproj
  apply cochainKernelLiftX_comp_eq (tensorCubeHighMixed2_inclusion S hS hproj)
  rw [← cochainTensorTripleDegreeMap_eq S.g (𝟙 S.X₂) S.g n]
  simp only [tensorCubeHighMixedRawSection0X, cochainTensorTripleDegreeMap_comp,
    tensorCubeHighMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_third, zero_comp]

lemma tensorCubeHighMixedSection1X_component0 (n : ℤ) :
    tensorCubeHighMixedSection1X S σ n ≫ (tensorCubeHighMixed0 S hS hproj).f n = 0 := by
  have := tensorCubeHighMixed0_target_inclusion_mono S hS hproj
  apply cochainKernelLiftX_comp_eq (tensorCubeHighMixed0_inclusion S hS hproj)
  rw [← cochainTensorTripleDegreeMap_eq S.g S.g (𝟙 S.X₂) n]
  simp only [tensorCubeHighMixedRawSection1X, cochainTensorTripleDegreeMap_comp,
    tensorCubeHighMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_first, zero_comp]

lemma tensorCubeHighMixedSection1X_component1 (n : ℤ) :
    tensorCubeHighMixedSection1X S σ n ≫ (tensorCubeHighMixed1 S hS hproj).f n = 𝟙 _ := by
  have := tensorCubeHighMixed1_target_inclusion_mono S hS hproj
  apply cochainKernelLiftX_comp_eq (tensorCubeHighMixed1_inclusion S hS hproj)
  rw [id_comp, ← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) S.g S.g n]
  rw [tensorCubeHighMixedRawSection1X, cochainTensorTripleDegreeMap_comp]
  simp only [HomologicalComplex.id_f, comp_id]
  rw [cochainSplitting_s_g]
  exact cochainTensorTripleDegreeMap_eq S.f (𝟙 S.X₃) (𝟙 S.X₃) n

lemma tensorCubeHighMixedSection1X_component2 (n : ℤ) :
    tensorCubeHighMixedSection1X S σ n ≫ (tensorCubeHighMixed2 S hS hproj).f n = 0 := by
  have := tensorCubeHighMixed2_target_inclusion_mono S hS hproj
  apply cochainKernelLiftX_comp_eq (tensorCubeHighMixed2_inclusion S hS hproj)
  rw [← cochainTensorTripleDegreeMap_eq S.g (𝟙 S.X₂) S.g n]
  simp only [tensorCubeHighMixedRawSection1X, cochainTensorTripleDegreeMap_comp,
    tensorCubeHighMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_first, zero_comp]

lemma tensorCubeHighMixedSection2X_component0 (n : ℤ) :
    tensorCubeHighMixedSection2X S σ n ≫ (tensorCubeHighMixed0 S hS hproj).f n = 0 := by
  have := tensorCubeHighMixed0_target_inclusion_mono S hS hproj
  apply cochainKernelLiftX_comp_eq (tensorCubeHighMixed0_inclusion S hS hproj)
  rw [← cochainTensorTripleDegreeMap_eq S.g S.g (𝟙 S.X₂) n]
  simp only [tensorCubeHighMixedRawSection2X, cochainTensorTripleDegreeMap_comp,
    tensorCubeHighMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_second, zero_comp]

lemma tensorCubeHighMixedSection2X_component1 (n : ℤ) :
    tensorCubeHighMixedSection2X S σ n ≫ (tensorCubeHighMixed1 S hS hproj).f n = 0 := by
  have := tensorCubeHighMixed1_target_inclusion_mono S hS hproj
  apply cochainKernelLiftX_comp_eq (tensorCubeHighMixed1_inclusion S hS hproj)
  rw [← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) S.g S.g n]
  simp only [tensorCubeHighMixedRawSection2X, cochainTensorTripleDegreeMap_comp,
    tensorCubeHighMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_second, zero_comp]

lemma tensorCubeHighMixedSection2X_component2 (n : ℤ) :
    tensorCubeHighMixedSection2X S σ n ≫ (tensorCubeHighMixed2 S hS hproj).f n = 𝟙 _ := by
  have := tensorCubeHighMixed2_target_inclusion_mono S hS hproj
  apply cochainKernelLiftX_comp_eq (tensorCubeHighMixed2_inclusion S hS hproj)
  rw [id_comp, ← cochainTensorTripleDegreeMap_eq S.g (𝟙 S.X₂) S.g n]
  rw [tensorCubeHighMixedRawSection2X, cochainTensorTripleDegreeMap_comp]
  simp only [HomologicalComplex.id_f, comp_id]
  rw [cochainSplitting_s_g]
  exact cochainTensorTripleDegreeMap_eq (𝟙 S.X₃) S.f (𝟙 S.X₃) n

end Adams
end SerrePositivity

end TensorCubeHighMixedSectionsPart

section TensorCubeHighMixedEpiPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
namespace Adams
variable {R : Type u} [CommRing R]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting)
    (hS : S.ShortExact) (hproj : ∀ i, Module.Projective R (S.X₃.X i))

abbrev tensorCubeHighMixedProjection0X (n : ℤ) :
    (tensorCubeHighMixedTarget S).X n ⟶ (cochainTensor (cochainTensor S.X₃ S.X₃) S.X₁).X n :=
  (biprod.fst : tensorCubeHighMixedTarget S ⟶ cochainTensor (cochainTensor S.X₃ S.X₃) S.X₁).f n

abbrev tensorCubeHighMixedProjection1X (n : ℤ) :
    (tensorCubeHighMixedTarget S).X n ⟶ (cochainTensor (cochainTensor S.X₁ S.X₃) S.X₃).X n :=
  ((biprod.snd ≫ biprod.fst) : tensorCubeHighMixedTarget S ⟶
    cochainTensor (cochainTensor S.X₁ S.X₃) S.X₃).f n

abbrev tensorCubeHighMixedProjection2X (n : ℤ) :
    (tensorCubeHighMixedTarget S).X n ⟶ (cochainTensor (cochainTensor S.X₃ S.X₁) S.X₃).X n :=
  ((biprod.snd ≫ biprod.snd) : tensorCubeHighMixedTarget S ⟶
    cochainTensor (cochainTensor S.X₃ S.X₁) S.X₃).f n

@[reassoc]
lemma tensorCubeHighMixedMap_projection0X (n : ℤ) :
    (tensorCubeHighMixedMap S hS hproj).f n ≫ tensorCubeHighMixedProjection0X S n =
      (tensorCubeHighMixed0 S hS hproj).f n := by
  rw [← HomologicalComplex.comp_f, tensorCubeHighMixedMap, biprod.lift_fst]

@[reassoc]
lemma tensorCubeHighMixedMap_projection1X (n : ℤ) :
    (tensorCubeHighMixedMap S hS hproj).f n ≫ tensorCubeHighMixedProjection1X S n =
      (tensorCubeHighMixed1 S hS hproj).f n := by
  rw [← HomologicalComplex.comp_f, tensorCubeHighMixedMap, biprod.lift_snd_assoc, biprod.lift_fst]

@[reassoc]
lemma tensorCubeHighMixedMap_projection2X (n : ℤ) :
    (tensorCubeHighMixedMap S hS hproj).f n ≫ tensorCubeHighMixedProjection2X S n =
      (tensorCubeHighMixed2 S hS hproj).f n := by
  rw [← HomologicalComplex.comp_f, tensorCubeHighMixedMap, biprod.lift_snd_assoc, biprod.lift_snd]

/-- The three graded component lifts form a section of the combined mixed quotient. -/
def tensorCubeHighMixedSectionX (n : ℤ) :
    (tensorCubeHighMixedTarget S).X n ⟶ (tensorCubeKernel S.g).X n :=
  tensorCubeHighMixedProjection0X S n ≫ tensorCubeHighMixedSection0X S σ n +
    tensorCubeHighMixedProjection1X S n ≫ tensorCubeHighMixedSection1X S σ n +
    tensorCubeHighMixedProjection2X S n ≫ tensorCubeHighMixedSection2X S σ n

set_option maxHeartbeats 600000 in
-- All three inverse equations compare evaluated biproduct and iterated kernel models.
lemma tensorCubeHighMixedSectionX_section (n : ℤ) :
    tensorCubeHighMixedSectionX S σ n ≫ (tensorCubeHighMixedMap S hS hproj).f n = 𝟙 _ := by
  apply cochainBiprodDegree_hom_ext (cochainTensor (cochainTensor S.X₃ S.X₃) S.X₁)
    (cochainTensor (cochainTensor S.X₁ S.X₃) S.X₃ ⊞ cochainTensor (cochainTensor S.X₃ S.X₁) S.X₃) n
  · rw [Category.assoc, tensorCubeHighMixedMap_projection0X, id_comp]
    exact section_sum0 _ _ _ _ _ _ _
      (tensorCubeHighMixedSection0X_component0 S σ hS hproj n)
      (tensorCubeHighMixedSection1X_component0 S σ hS hproj n)
      (tensorCubeHighMixedSection2X_component0 S σ hS hproj n)
  · apply cochainBiprodDegree_hom_ext (cochainTensor (cochainTensor S.X₁ S.X₃) S.X₃)
      (cochainTensor (cochainTensor S.X₃ S.X₁) S.X₃) n
    · rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f,
        tensorCubeHighMixedMap_projection1X]
      simp only [id_comp]
      exact section_sum1 _ _ _ _ _ _ _
        (tensorCubeHighMixedSection0X_component1 S σ hS hproj n)
        (tensorCubeHighMixedSection1X_component1 S σ hS hproj n)
        (tensorCubeHighMixedSection2X_component1 S σ hS hproj n)
    · rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f,
        tensorCubeHighMixedMap_projection2X]
      simp only [id_comp]
      exact section_sum2 _ _ _ _ _ _ _
        (tensorCubeHighMixedSection0X_component2 S σ hS hproj n)
        (tensorCubeHighMixedSection1X_component2 S σ hS hproj n)
        (tensorCubeHighMixedSection2X_component2 S σ hS hproj n)

omit σ in
lemma tensorCubeHighMixedMap_epi : Epi (tensorCubeHighMixedMap S hS hproj) := by
  let σ := cochainDegreewiseSplittingOfProjective S hS hproj
  apply HomologicalComplex.epi_of_epi_f
  intro n
  exact epi_of_epi_fac (tensorCubeHighMixedSectionX_section S σ hS hproj n)

end Adams
end SerrePositivity

end TensorCubeHighMixedEpiPart

section TensorCubeHighMixedKernelPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits
namespace Adams
variable {R : Type u} [CommRing R]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (hS : S.ShortExact) (hproj : ∀ i, Module.Projective R (S.X₃.X i))

@[simp, reassoc]
lemma tensorCubeFirstLayerToKernel_highMixed1 :
    tensorCubeFirstLayerToKernel S.g ≫ tensorCubeHighMixed1 S hS hproj = 0 := by
  have := tensorCubeHighMixed1_target_inclusion_mono S hS hproj
  apply (cancel_mono (cochainTensorTripleMap S.f (𝟙 S.X₃) (𝟙 S.X₃))).mp
  rw [Category.assoc, tensorCubeHighMixed1_inclusion,
    tensorCubeFirstLayerToKernel_inclusion_assoc, tensorCubeFirstLayerInclusion_pair1]
  simp only [zero_comp]

@[simp, reassoc]
lemma tensorCubeFirstLayerToKernel_highMixed2 :
    tensorCubeFirstLayerToKernel S.g ≫ tensorCubeHighMixed2 S hS hproj = 0 := by
  have := tensorCubeHighMixed2_target_inclusion_mono S hS hproj
  apply (cancel_mono (cochainTensorTripleMap (𝟙 S.X₃) S.f (𝟙 S.X₃))).mp
  rw [Category.assoc, tensorCubeHighMixed2_inclusion,
    tensorCubeFirstLayerToKernel_inclusion_assoc, tensorCubeFirstLayerInclusion_pair2]
  simp only [zero_comp]

@[simp]
lemma tensorCubeFirstLayerToKernel_highMixedMap :
    tensorCubeFirstLayerToKernel S.g ≫ tensorCubeHighMixedMap S hS hproj = 0 := by
  apply biprod.hom_ext
  · simp only [tensorCubeHighMixedMap, Category.assoc, biprod.lift_fst,
      tensorCubeFirstLayerToKernel_highMixed0, zero_comp]
  · apply biprod.hom_ext
    · simp only [tensorCubeHighMixedMap, Category.assoc, biprod.lift_snd_assoc,
        biprod.lift_fst, tensorCubeFirstLayerToKernel_highMixed1, zero_comp]
    · simp only [tensorCubeHighMixedMap, Category.assoc,
        biprod.lift_snd, tensorCubeFirstLayerToKernel_highMixed2, zero_comp]

lemma tensorCubeHighMixedMap_kernel_pair_zero
    {W : CochainComplex (ModuleCat.{u} R) ℤ} (v : W ⟶ tensorCubeKernel S.g)
    (hv : v ≫ tensorCubeHighMixedMap S hS hproj = 0) :
    (v ≫ tensorCubeKernelInclusion S.g) ≫ tensorCubePairMap S.g = 0 := by
  have h₀ : v ≫ tensorCubeHighMixed0 S hS hproj = 0 := by
    simpa only [tensorCubeHighMixedMap, Category.assoc, biprod.lift_fst, zero_comp] using
      hv =≫ biprod.fst
  have h₁ : v ≫ tensorCubeHighMixed1 S hS hproj = 0 := by
    simpa only [tensorCubeHighMixedMap, Category.assoc, biprod.lift_snd_assoc,
      biprod.lift_fst, zero_comp] using hv =≫ (biprod.snd ≫ biprod.fst)
  have h₂ : v ≫ tensorCubeHighMixed2 S hS hproj = 0 := by
    simpa only [tensorCubeHighMixedMap, Category.assoc, biprod.lift_snd_assoc,
      biprod.lift_snd, zero_comp] using hv =≫ (biprod.snd ≫ biprod.snd)
  apply biprod.hom_ext
  · simp only [tensorCubePairMap, Category.assoc, biprod.lift_fst, zero_comp]
    rw [← tensorCubeHighMixed0_inclusion S hS hproj, ← Category.assoc, h₀, zero_comp]
  · apply biprod.hom_ext
    · simp only [tensorCubePairMap, Category.assoc, biprod.lift_snd_assoc,
        biprod.lift_fst, zero_comp]
      rw [← tensorCubeHighMixed1_inclusion S hS hproj, ← Category.assoc, h₁, zero_comp]
    · simp only [tensorCubePairMap, Category.assoc,
        biprod.lift_snd, zero_comp]
      rw [← tensorCubeHighMixed2_inclusion S hS hproj, ← Category.assoc, h₂, zero_comp]

/-- A morphism killed by the high mixed quotient factors through the first layer. -/
def tensorCubeHighMixedKernelLift
    {W : CochainComplex (ModuleCat.{u} R) ℤ} (v : W ⟶ tensorCubeKernel S.g)
    (hv : v ≫ tensorCubeHighMixedMap S hS hproj = 0) : W ⟶ tensorCubeFirstLayer S.g :=
  kernel.lift (tensorCubePairMap S.g) (v ≫ tensorCubeKernelInclusion S.g)
    (tensorCubeHighMixedMap_kernel_pair_zero S hS hproj v hv)

lemma tensorCubeHighMixedKernelLift_fac
    {W : CochainComplex (ModuleCat.{u} R) ℤ} (v : W ⟶ tensorCubeKernel S.g)
    (hv : v ≫ tensorCubeHighMixedMap S hS hproj = 0) :
    tensorCubeHighMixedKernelLift S hS hproj v hv ≫ tensorCubeFirstLayerToKernel S.g = v := by
  apply (cancel_mono (tensorCubeKernelInclusion S.g)).mp
  rw [Category.assoc, tensorCubeFirstLayerToKernel_inclusion,
    tensorCubeHighMixedKernelLift, kernel.lift_ι]

abbrev tensorCubeHighMixedShortComplex :=
  ShortComplex.mk (tensorCubeFirstLayerToKernel S.g) (tensorCubeHighMixedMap S hS hproj)
    (tensorCubeFirstLayerToKernel_highMixedMap S hS hproj)

set_option maxHeartbeats 600000 in
-- Compare the kernel-fork model with the first-layer inclusion into the outer kernel.
/-- The first layer is the kernel of the high mixed quotient. -/
def tensorCubeHighMixedIsKernel :
    IsLimit (KernelFork.ofι (tensorCubeFirstLayerToKernel S.g)
      (tensorCubeFirstLayerToKernel_highMixedMap S hS hproj)) :=
  KernelFork.IsLimit.ofι' (tensorCubeFirstLayerToKernel S.g)
    (tensorCubeFirstLayerToKernel_highMixedMap S hS hproj) (fun v hv =>
    ⟨tensorCubeHighMixedKernelLift S hS hproj v hv,
      tensorCubeHighMixedKernelLift_fac S hS hproj v hv⟩)

set_option maxHeartbeats 600000 in
-- Identify the kernel fork with the short-complex fields when transferring exactness.
lemma tensorCubeHighMixedShortComplex_shortExact :
    (tensorCubeHighMixedShortComplex S hS hproj).ShortExact := by
  have := tensorCubeHighMixedMap_epi S hS hproj
  refine { exact := ?_ }
  exact ShortComplex.exact_of_f_is_kernel
    (tensorCubeHighMixedShortComplex S hS hproj) (tensorCubeHighMixedIsKernel S hS hproj)

end Adams
end SerrePositivity

end TensorCubeHighMixedKernelPart

section TensorCubeHighMixedQuotientPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits
namespace Adams
variable {R : Type u} [CommRing R]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))

lemma tensorCubeHighMixedTarget_perfect
    (ha : strictlyPerfectComplex R S.X₁) (hd : strictlyPerfectComplex R S.X₃) :
    strictlyPerfectComplex R (tensorCubeHighMixedTarget S) :=
  cochainTensorCyclicSum_perfect _ _ _ hd hd ha

lemma tensorCubeHighMixedTarget_support
    {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (ha : strictlyPerfectComplex R S.X₁) (hd : strictlyPerfectComplex R S.X₃)
    (hsA : HasHomologySupportOn Z S.X₁) (hsD : HasHomologySupportOn Z S.X₃) :
    HasHomologySupportOn Z (tensorCubeHighMixedTarget S) :=
  cochainTensorCyclicSum_support _ _ _ hd hd ha hsD hsD hsA

abbrev tensorCubeHighMixedRotation : tensorCubeHighMixedTarget S ⟶ tensorCubeHighMixedTarget S :=
  cochainTensorCyclicSumRotation S.X₃ S.X₃ S.X₁

abbrev tensorCubeHighMixedAction : CochainCubicAction (tensorCubeHighMixedTarget S) :=
  cochainTensorCyclicSumAction S.X₃ S.X₃ S.X₁

variable (hS : S.ShortExact) (hproj : ∀ i, Module.Projective R (S.X₃.X i))

set_option maxHeartbeats 600000 in
-- Compare the combined tensor maps with the nested biproduct rotation.
lemma tensorCubeHighMixedMap_rotation :
    tensorCubeKernelRotation S.g ≫ tensorCubeHighMixedMap S hS hproj =
      tensorCubeHighMixedMap S hS hproj ≫ tensorCubeHighMixedRotation S :=
  three_components_rotation (tensorCubeKernelRotation S.g)
    (tensorCubeHighMixed0 S hS hproj) (tensorCubeHighMixed1 S hS hproj)
    (tensorCubeHighMixed2 S hS hproj) (cochainTensorRotationIso S.X₃ S.X₃ S.X₁).hom
    (cochainTensorRotationIso S.X₁ S.X₃ S.X₃).hom
    (cochainTensorRotationIso S.X₃ S.X₁ S.X₃).hom
    (tensorCubeKernelRotation_highMixed0 S hS hproj)
    (tensorCubeKernelRotation_highMixed1 S hS hproj)
    (tensorCubeKernelRotation_highMixed2 S hS hproj)

end Adams
end SerrePositivity

end TensorCubeHighMixedQuotientPart
