module

public import SerrePositivity.KTheory.Adams.TensorCubeHighMixedComponents
public import SerrePositivity.PerfectComplex.TensorTripleDegreeMaps
public import SerrePositivity.PerfectComplex.DegreewiseKernelLift

/-! # Degreewise lifts of the high mixed tensor-cube quotient -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
namespace Adams
variable {R : Type u} [CommRing R]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting)

lemma tensorCubeHighMixedSplitting_f_g :
    (fun i => S.f.f i ≫ S.g.f i) = (fun i => (0 : S.X₁.X i ⟶ S.X₃.X i)) := by
  funext i
  exact congrArg (fun f => f.f i) S.zero

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
  apply (cancel_mono ((cochainTensorTripleMap (𝟙 S.X₃) (𝟙 S.X₃) S.f).f n)).mp
  rw [Category.assoc, ← HomologicalComplex.comp_f, tensorCubeHighMixed0_inclusion,
    HomologicalComplex.comp_f, tensorCubeHighMixedSection0X_inclusion_assoc,
    id_comp,
    ← cochainTensorTripleDegreeMap_eq S.g S.g (𝟙 S.X₂) n]
  rw [tensorCubeHighMixedRawSection0X, cochainTensorTripleDegreeMap_comp]
  simp only [HomologicalComplex.id_f, comp_id]
  have he : (fun i => cochainSplittingSection S σ i ≫ S.g.f i) =
      (fun i => 𝟙 (S.X₃.X i)) := funext fun i => (σ i).s_g
  rw [he]
  exact cochainTensorTripleDegreeMap_eq (𝟙 S.X₃) (𝟙 S.X₃) S.f n

lemma tensorCubeHighMixedSection0X_component1 (n : ℤ) :
    tensorCubeHighMixedSection0X S σ n ≫ (tensorCubeHighMixed1 S hS hproj).f n = 0 := by
  have := tensorCubeHighMixed1_target_inclusion_mono S hS hproj
  apply (cancel_mono ((cochainTensorTripleMap S.f (𝟙 S.X₃) (𝟙 S.X₃)).f n)).mp
  rw [Category.assoc, ← HomologicalComplex.comp_f, tensorCubeHighMixed1_inclusion,
    HomologicalComplex.comp_f, tensorCubeHighMixedSection0X_inclusion_assoc,
    ← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) S.g S.g n]
  simp only [tensorCubeHighMixedRawSection0X, cochainTensorTripleDegreeMap_comp,
    tensorCubeHighMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_third, zero_comp]

lemma tensorCubeHighMixedSection0X_component2 (n : ℤ) :
    tensorCubeHighMixedSection0X S σ n ≫ (tensorCubeHighMixed2 S hS hproj).f n = 0 := by
  have := tensorCubeHighMixed2_target_inclusion_mono S hS hproj
  apply (cancel_mono ((cochainTensorTripleMap (𝟙 S.X₃) S.f (𝟙 S.X₃)).f n)).mp
  rw [Category.assoc, ← HomologicalComplex.comp_f, tensorCubeHighMixed2_inclusion,
    HomologicalComplex.comp_f, tensorCubeHighMixedSection0X_inclusion_assoc,
    ← cochainTensorTripleDegreeMap_eq S.g (𝟙 S.X₂) S.g n]
  simp only [tensorCubeHighMixedRawSection0X, cochainTensorTripleDegreeMap_comp,
    tensorCubeHighMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_third, zero_comp]

lemma tensorCubeHighMixedSection1X_component0 (n : ℤ) :
    tensorCubeHighMixedSection1X S σ n ≫ (tensorCubeHighMixed0 S hS hproj).f n = 0 := by
  have := tensorCubeHighMixed0_target_inclusion_mono S hS hproj
  apply (cancel_mono ((cochainTensorTripleMap (𝟙 S.X₃) (𝟙 S.X₃) S.f).f n)).mp
  rw [Category.assoc, ← HomologicalComplex.comp_f, tensorCubeHighMixed0_inclusion,
    HomologicalComplex.comp_f, tensorCubeHighMixedSection1X_inclusion_assoc,
    ← cochainTensorTripleDegreeMap_eq S.g S.g (𝟙 S.X₂) n]
  simp only [tensorCubeHighMixedRawSection1X, cochainTensorTripleDegreeMap_comp,
    tensorCubeHighMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_first, zero_comp]

lemma tensorCubeHighMixedSection1X_component1 (n : ℤ) :
    tensorCubeHighMixedSection1X S σ n ≫ (tensorCubeHighMixed1 S hS hproj).f n = 𝟙 _ := by
  have := tensorCubeHighMixed1_target_inclusion_mono S hS hproj
  apply (cancel_mono ((cochainTensorTripleMap S.f (𝟙 S.X₃) (𝟙 S.X₃)).f n)).mp
  rw [Category.assoc, ← HomologicalComplex.comp_f, tensorCubeHighMixed1_inclusion,
    HomologicalComplex.comp_f, tensorCubeHighMixedSection1X_inclusion_assoc,
    id_comp,
    ← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) S.g S.g n]
  rw [tensorCubeHighMixedRawSection1X, cochainTensorTripleDegreeMap_comp]
  simp only [HomologicalComplex.id_f, comp_id]
  have he : (fun i => cochainSplittingSection S σ i ≫ S.g.f i) =
      (fun i => 𝟙 (S.X₃.X i)) := funext fun i => (σ i).s_g
  rw [he]
  exact cochainTensorTripleDegreeMap_eq S.f (𝟙 S.X₃) (𝟙 S.X₃) n

lemma tensorCubeHighMixedSection1X_component2 (n : ℤ) :
    tensorCubeHighMixedSection1X S σ n ≫ (tensorCubeHighMixed2 S hS hproj).f n = 0 := by
  have := tensorCubeHighMixed2_target_inclusion_mono S hS hproj
  apply (cancel_mono ((cochainTensorTripleMap (𝟙 S.X₃) S.f (𝟙 S.X₃)).f n)).mp
  rw [Category.assoc, ← HomologicalComplex.comp_f, tensorCubeHighMixed2_inclusion,
    HomologicalComplex.comp_f, tensorCubeHighMixedSection1X_inclusion_assoc,
    ← cochainTensorTripleDegreeMap_eq S.g (𝟙 S.X₂) S.g n]
  simp only [tensorCubeHighMixedRawSection1X, cochainTensorTripleDegreeMap_comp,
    tensorCubeHighMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_first, zero_comp]

lemma tensorCubeHighMixedSection2X_component0 (n : ℤ) :
    tensorCubeHighMixedSection2X S σ n ≫ (tensorCubeHighMixed0 S hS hproj).f n = 0 := by
  have := tensorCubeHighMixed0_target_inclusion_mono S hS hproj
  apply (cancel_mono ((cochainTensorTripleMap (𝟙 S.X₃) (𝟙 S.X₃) S.f).f n)).mp
  rw [Category.assoc, ← HomologicalComplex.comp_f, tensorCubeHighMixed0_inclusion,
    HomologicalComplex.comp_f, tensorCubeHighMixedSection2X_inclusion_assoc,
    ← cochainTensorTripleDegreeMap_eq S.g S.g (𝟙 S.X₂) n]
  simp only [tensorCubeHighMixedRawSection2X, cochainTensorTripleDegreeMap_comp,
    tensorCubeHighMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_second, zero_comp]

lemma tensorCubeHighMixedSection2X_component1 (n : ℤ) :
    tensorCubeHighMixedSection2X S σ n ≫ (tensorCubeHighMixed1 S hS hproj).f n = 0 := by
  have := tensorCubeHighMixed1_target_inclusion_mono S hS hproj
  apply (cancel_mono ((cochainTensorTripleMap S.f (𝟙 S.X₃) (𝟙 S.X₃)).f n)).mp
  rw [Category.assoc, ← HomologicalComplex.comp_f, tensorCubeHighMixed1_inclusion,
    HomologicalComplex.comp_f, tensorCubeHighMixedSection2X_inclusion_assoc,
    ← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) S.g S.g n]
  simp only [tensorCubeHighMixedRawSection2X, cochainTensorTripleDegreeMap_comp,
    tensorCubeHighMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_second, zero_comp]

lemma tensorCubeHighMixedSection2X_component2 (n : ℤ) :
    tensorCubeHighMixedSection2X S σ n ≫ (tensorCubeHighMixed2 S hS hproj).f n = 𝟙 _ := by
  have := tensorCubeHighMixed2_target_inclusion_mono S hS hproj
  apply (cancel_mono ((cochainTensorTripleMap (𝟙 S.X₃) S.f (𝟙 S.X₃)).f n)).mp
  rw [Category.assoc, ← HomologicalComplex.comp_f, tensorCubeHighMixed2_inclusion,
    HomologicalComplex.comp_f, tensorCubeHighMixedSection2X_inclusion_assoc,
    id_comp,
    ← cochainTensorTripleDegreeMap_eq S.g (𝟙 S.X₂) S.g n]
  rw [tensorCubeHighMixedRawSection2X, cochainTensorTripleDegreeMap_comp]
  simp only [HomologicalComplex.id_f, comp_id]
  have he : (fun i => cochainSplittingSection S σ i ≫ S.g.f i) =
      (fun i => 𝟙 (S.X₃.X i)) := funext fun i => (σ i).s_g
  rw [he]
  exact cochainTensorTripleDegreeMap_eq (𝟙 S.X₃) S.f (𝟙 S.X₃) n

end Adams
end SerrePositivity
