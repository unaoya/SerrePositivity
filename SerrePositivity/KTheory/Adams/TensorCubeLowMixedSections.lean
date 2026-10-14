module

public import SerrePositivity.KTheory.Adams.TensorCubeLowMixedInclusions

/-! # Degreewise lifts of the low mixed tensor-cube quotient -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
namespace Adams
private lemma section_sum0 {C : Type*} [Category C] [Preadditive C]
    {W K Y₀ Y₁ Y₂ : C} (p₀ : W ⟶ Y₀) (p₁ : W ⟶ Y₁) (p₂ : W ⟶ Y₂)
    (d₀ : Y₀ ⟶ K) (d₁ : Y₁ ⟶ K) (d₂ : Y₂ ⟶ K) (m : K ⟶ Y₀)
    (h₀ : d₀ ≫ m = 𝟙 _) (h₁ : d₁ ≫ m = 0) (h₂ : d₂ ≫ m = 0) :
    (p₀ ≫ d₀ + p₁ ≫ d₁ + p₂ ≫ d₂) ≫ m = p₀ := by
  rw [add_comp, add_comp, Category.assoc, Category.assoc, Category.assoc, h₀, h₁, h₂]
  simp only [comp_id, comp_zero, add_zero]

private lemma section_sum1 {C : Type*} [Category C] [Preadditive C]
    {W K Y₀ Y₁ Y₂ : C} (p₀ : W ⟶ Y₀) (p₁ : W ⟶ Y₁) (p₂ : W ⟶ Y₂)
    (d₀ : Y₀ ⟶ K) (d₁ : Y₁ ⟶ K) (d₂ : Y₂ ⟶ K) (m : K ⟶ Y₁)
    (h₀ : d₀ ≫ m = 0) (h₁ : d₁ ≫ m = 𝟙 _) (h₂ : d₂ ≫ m = 0) :
    (p₀ ≫ d₀ + p₁ ≫ d₁ + p₂ ≫ d₂) ≫ m = p₁ := by
  rw [add_comp, add_comp, Category.assoc, Category.assoc, Category.assoc, h₀, h₁, h₂]
  simp only [comp_id, comp_zero, zero_add, add_zero]

private lemma section_sum2 {C : Type*} [Category C] [Preadditive C]
    {W K Y₀ Y₁ Y₂ : C} (p₀ : W ⟶ Y₀) (p₁ : W ⟶ Y₁) (p₂ : W ⟶ Y₂)
    (d₀ : Y₀ ⟶ K) (d₁ : Y₁ ⟶ K) (d₂ : Y₂ ⟶ K) (m : K ⟶ Y₂)
    (h₀ : d₀ ≫ m = 0) (h₁ : d₁ ≫ m = 0) (h₂ : d₂ ≫ m = 𝟙 _) :
    (p₀ ≫ d₀ + p₁ ≫ d₁ + p₂ ≫ d₂) ≫ m = p₂ := by
  rw [add_comp, add_comp, Category.assoc, Category.assoc, Category.assoc, h₀, h₁, h₂]
  simp only [comp_id, comp_zero, zero_add, add_zero]

variable {R : Type u} [CommRing R]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting)

lemma tensorCubeLowMixedSplitting_f_g :
    (fun i => S.f.f i ≫ S.g.f i) = (fun i => (0 : S.X₁.X i ⟶ S.X₃.X i)) := by
  funext i
  exact congrArg (fun f => f.f i) S.zero

/-- Lift a DAA component into the cube using the degreewise quotient section. -/
def tensorCubeLowMixedRawSection0X (n : ℤ) :
    (cochainTensor (cochainTensor S.X₃ S.X₁) S.X₁).X n ⟶ (tensorCube S.X₂).X n :=
  cochainTensorTripleDegreeMap (cochainSplittingSection S σ) S.f.f S.f.f n

lemma tensorCubeLowMixedRawSection0X_pairMap_zero (n : ℤ) :
    tensorCubeLowMixedRawSection0X S σ n ≫ (tensorCubePairMap S.g).f n = 0 := by
  apply cochainBiprodDegree_hom_ext (cochainTensor (cochainTensor S.X₃ S.X₃) S.X₂)
    (cochainTensor (cochainTensor S.X₂ S.X₃) S.X₃ ⊞
      cochainTensor (cochainTensor S.X₃ S.X₂) S.X₃) n
  · rw [Category.assoc, ← HomologicalComplex.comp_f, tensorCubePairMap, biprod.lift_fst,
      ← cochainTensorTripleDegreeMap_eq S.g S.g (𝟙 S.X₂) n]
    simp only [tensorCubeLowMixedRawSection0X, cochainTensorTripleDegreeMap_comp,
      tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_second, zero_comp]
  · apply cochainBiprodDegree_hom_ext (cochainTensor (cochainTensor S.X₂ S.X₃) S.X₃)
      (cochainTensor (cochainTensor S.X₃ S.X₂) S.X₃) n
    · rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f,
        ← HomologicalComplex.comp_f, tensorCubePairMap, biprod.lift_snd_assoc, biprod.lift_fst,
        ← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) S.g S.g n]
      simp only [tensorCubeLowMixedRawSection0X, cochainTensorTripleDegreeMap_comp,
        tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_second, zero_comp]
    · rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f,
        ← HomologicalComplex.comp_f, tensorCubePairMap, biprod.lift_snd_assoc, biprod.lift_snd,
        ← cochainTensorTripleDegreeMap_eq S.g (𝟙 S.X₂) S.g n]
      simp only [tensorCubeLowMixedRawSection0X, cochainTensorTripleDegreeMap_comp,
        tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_third, zero_comp]

/-- The DAA graded component belongs to the first intermediate kernel. -/
def tensorCubeLowMixedSection0X (n : ℤ) :
    (cochainTensor (cochainTensor S.X₃ S.X₁) S.X₁).X n ⟶ (tensorCubeFirstLayer S.g).X n :=
  cochainKernelLiftX (tensorCubePairMap S.g) n (tensorCubeLowMixedRawSection0X S σ n)
    (tensorCubeLowMixedRawSection0X_pairMap_zero S σ n)

@[reassoc]
lemma tensorCubeLowMixedSection0X_inclusion (n : ℤ) :
    tensorCubeLowMixedSection0X S σ n ≫ (tensorCubeFirstLayerInclusion S.g).f n =
      tensorCubeLowMixedRawSection0X S σ n := cochainKernelLiftX_inclusion _ _ _ _

/-- Lift a ADA component into the cube using the degreewise quotient section. -/
def tensorCubeLowMixedRawSection1X (n : ℤ) :
    (cochainTensor (cochainTensor S.X₁ S.X₃) S.X₁).X n ⟶ (tensorCube S.X₂).X n :=
  cochainTensorTripleDegreeMap S.f.f (cochainSplittingSection S σ) S.f.f n

lemma tensorCubeLowMixedRawSection1X_pairMap_zero (n : ℤ) :
    tensorCubeLowMixedRawSection1X S σ n ≫ (tensorCubePairMap S.g).f n = 0 := by
  apply cochainBiprodDegree_hom_ext (cochainTensor (cochainTensor S.X₃ S.X₃) S.X₂)
    (cochainTensor (cochainTensor S.X₂ S.X₃) S.X₃ ⊞
      cochainTensor (cochainTensor S.X₃ S.X₂) S.X₃) n
  · rw [Category.assoc, ← HomologicalComplex.comp_f, tensorCubePairMap, biprod.lift_fst,
      ← cochainTensorTripleDegreeMap_eq S.g S.g (𝟙 S.X₂) n]
    simp only [tensorCubeLowMixedRawSection1X, cochainTensorTripleDegreeMap_comp,
      tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_first, zero_comp]
  · apply cochainBiprodDegree_hom_ext (cochainTensor (cochainTensor S.X₂ S.X₃) S.X₃)
      (cochainTensor (cochainTensor S.X₃ S.X₂) S.X₃) n
    · rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f,
        ← HomologicalComplex.comp_f, tensorCubePairMap, biprod.lift_snd_assoc, biprod.lift_fst,
        ← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) S.g S.g n]
      simp only [tensorCubeLowMixedRawSection1X, cochainTensorTripleDegreeMap_comp,
        tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_third, zero_comp]
    · rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f,
        ← HomologicalComplex.comp_f, tensorCubePairMap, biprod.lift_snd_assoc, biprod.lift_snd,
        ← cochainTensorTripleDegreeMap_eq S.g (𝟙 S.X₂) S.g n]
      simp only [tensorCubeLowMixedRawSection1X, cochainTensorTripleDegreeMap_comp,
        tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_first, zero_comp]

/-- The ADA graded component belongs to the first intermediate kernel. -/
def tensorCubeLowMixedSection1X (n : ℤ) :
    (cochainTensor (cochainTensor S.X₁ S.X₃) S.X₁).X n ⟶ (tensorCubeFirstLayer S.g).X n :=
  cochainKernelLiftX (tensorCubePairMap S.g) n (tensorCubeLowMixedRawSection1X S σ n)
    (tensorCubeLowMixedRawSection1X_pairMap_zero S σ n)

@[reassoc]
lemma tensorCubeLowMixedSection1X_inclusion (n : ℤ) :
    tensorCubeLowMixedSection1X S σ n ≫ (tensorCubeFirstLayerInclusion S.g).f n =
      tensorCubeLowMixedRawSection1X S σ n := cochainKernelLiftX_inclusion _ _ _ _

/-- Lift a AAD component into the cube using the degreewise quotient section. -/
def tensorCubeLowMixedRawSection2X (n : ℤ) :
    (cochainTensor (cochainTensor S.X₁ S.X₁) S.X₃).X n ⟶ (tensorCube S.X₂).X n :=
  cochainTensorTripleDegreeMap S.f.f S.f.f (cochainSplittingSection S σ) n

lemma tensorCubeLowMixedRawSection2X_pairMap_zero (n : ℤ) :
    tensorCubeLowMixedRawSection2X S σ n ≫ (tensorCubePairMap S.g).f n = 0 := by
  apply cochainBiprodDegree_hom_ext (cochainTensor (cochainTensor S.X₃ S.X₃) S.X₂)
    (cochainTensor (cochainTensor S.X₂ S.X₃) S.X₃ ⊞
      cochainTensor (cochainTensor S.X₃ S.X₂) S.X₃) n
  · rw [Category.assoc, ← HomologicalComplex.comp_f, tensorCubePairMap, biprod.lift_fst,
      ← cochainTensorTripleDegreeMap_eq S.g S.g (𝟙 S.X₂) n]
    simp only [tensorCubeLowMixedRawSection2X, cochainTensorTripleDegreeMap_comp,
      tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_first, zero_comp]
  · apply cochainBiprodDegree_hom_ext (cochainTensor (cochainTensor S.X₂ S.X₃) S.X₃)
      (cochainTensor (cochainTensor S.X₃ S.X₂) S.X₃) n
    · rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f,
        ← HomologicalComplex.comp_f, tensorCubePairMap, biprod.lift_snd_assoc, biprod.lift_fst,
        ← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) S.g S.g n]
      simp only [tensorCubeLowMixedRawSection2X, cochainTensorTripleDegreeMap_comp,
        tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_second, zero_comp]
    · rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f,
        ← HomologicalComplex.comp_f, tensorCubePairMap, biprod.lift_snd_assoc, biprod.lift_snd,
        ← cochainTensorTripleDegreeMap_eq S.g (𝟙 S.X₂) S.g n]
      simp only [tensorCubeLowMixedRawSection2X, cochainTensorTripleDegreeMap_comp,
        tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_first, zero_comp]

/-- The AAD graded component belongs to the first intermediate kernel. -/
def tensorCubeLowMixedSection2X (n : ℤ) :
    (cochainTensor (cochainTensor S.X₁ S.X₁) S.X₃).X n ⟶ (tensorCubeFirstLayer S.g).X n :=
  cochainKernelLiftX (tensorCubePairMap S.g) n (tensorCubeLowMixedRawSection2X S σ n)
    (tensorCubeLowMixedRawSection2X_pairMap_zero S σ n)

@[reassoc]
lemma tensorCubeLowMixedSection2X_inclusion (n : ℤ) :
    tensorCubeLowMixedSection2X S σ n ≫ (tensorCubeFirstLayerInclusion S.g).f n =
      tensorCubeLowMixedRawSection2X S σ n := cochainKernelLiftX_inclusion _ _ _ _

variable (hS : S.ShortExact) (hproj : ∀ i, Module.Projective R (S.X₃.X i))

lemma tensorCubeLowMixedSection0X_component0 (n : ℤ) :
    tensorCubeLowMixedSection0X S σ n ≫ (tensorCubeLowMixed0 S hS hproj).f n = 𝟙 _ := by
  have := tensorCubeLowMixed0_target_inclusion_mono S hS hproj
  apply (cancel_mono ((cochainTensorTripleMap (𝟙 S.X₃) S.f S.f).f n)).mp
  rw [Category.assoc, ← HomologicalComplex.comp_f, tensorCubeLowMixed0_inclusion,
    HomologicalComplex.comp_f, tensorCubeLowMixedSection0X_inclusion_assoc, id_comp,
    ← cochainTensorTripleDegreeMap_eq S.g (𝟙 S.X₂) (𝟙 S.X₂) n]
  rw [tensorCubeLowMixedRawSection0X, cochainTensorTripleDegreeMap_comp]
  simp only [HomologicalComplex.id_f, comp_id]
  have he : (fun i => cochainSplittingSection S σ i ≫ S.g.f i) =
      (fun i => 𝟙 (S.X₃.X i)) := funext fun i => (σ i).s_g
  rw [he]
  exact cochainTensorTripleDegreeMap_eq (𝟙 S.X₃) S.f S.f n

lemma tensorCubeLowMixedSection0X_component1 (n : ℤ) :
    tensorCubeLowMixedSection0X S σ n ≫ (tensorCubeLowMixed1 S hS hproj).f n = 0 := by
  have := tensorCubeLowMixed1_target_inclusion_mono S hS hproj
  apply (cancel_mono ((cochainTensorTripleMap S.f (𝟙 S.X₃) S.f).f n)).mp
  rw [Category.assoc, ← HomologicalComplex.comp_f, tensorCubeLowMixed1_inclusion,
    HomologicalComplex.comp_f, tensorCubeLowMixedSection0X_inclusion_assoc,
    ← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) S.g (𝟙 S.X₂) n]
  simp only [tensorCubeLowMixedRawSection0X, cochainTensorTripleDegreeMap_comp,
    tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_second, zero_comp]

lemma tensorCubeLowMixedSection0X_component2 (n : ℤ) :
    tensorCubeLowMixedSection0X S σ n ≫ (tensorCubeLowMixed2 S hS hproj).f n = 0 := by
  have := tensorCubeLowMixed2_target_inclusion_mono S hS hproj
  apply (cancel_mono ((cochainTensorTripleMap S.f S.f (𝟙 S.X₃)).f n)).mp
  rw [Category.assoc, ← HomologicalComplex.comp_f, tensorCubeLowMixed2_inclusion,
    HomologicalComplex.comp_f, tensorCubeLowMixedSection0X_inclusion_assoc,
    ← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) (𝟙 S.X₂) S.g n]
  simp only [tensorCubeLowMixedRawSection0X, cochainTensorTripleDegreeMap_comp,
    tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_third, zero_comp]

lemma tensorCubeLowMixedSection1X_component0 (n : ℤ) :
    tensorCubeLowMixedSection1X S σ n ≫ (tensorCubeLowMixed0 S hS hproj).f n = 0 := by
  have := tensorCubeLowMixed0_target_inclusion_mono S hS hproj
  apply (cancel_mono ((cochainTensorTripleMap (𝟙 S.X₃) S.f S.f).f n)).mp
  rw [Category.assoc, ← HomologicalComplex.comp_f, tensorCubeLowMixed0_inclusion,
    HomologicalComplex.comp_f, tensorCubeLowMixedSection1X_inclusion_assoc,
    ← cochainTensorTripleDegreeMap_eq S.g (𝟙 S.X₂) (𝟙 S.X₂) n]
  simp only [tensorCubeLowMixedRawSection1X, cochainTensorTripleDegreeMap_comp,
    tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_first, zero_comp]

lemma tensorCubeLowMixedSection1X_component1 (n : ℤ) :
    tensorCubeLowMixedSection1X S σ n ≫ (tensorCubeLowMixed1 S hS hproj).f n = 𝟙 _ := by
  have := tensorCubeLowMixed1_target_inclusion_mono S hS hproj
  apply (cancel_mono ((cochainTensorTripleMap S.f (𝟙 S.X₃) S.f).f n)).mp
  rw [Category.assoc, ← HomologicalComplex.comp_f, tensorCubeLowMixed1_inclusion,
    HomologicalComplex.comp_f, tensorCubeLowMixedSection1X_inclusion_assoc,
    id_comp, ← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) S.g (𝟙 S.X₂) n]
  rw [tensorCubeLowMixedRawSection1X, cochainTensorTripleDegreeMap_comp]
  simp only [HomologicalComplex.id_f, comp_id]
  have he : (fun i => cochainSplittingSection S σ i ≫ S.g.f i) =
      (fun i => 𝟙 (S.X₃.X i)) := funext fun i => (σ i).s_g
  rw [he]
  exact cochainTensorTripleDegreeMap_eq S.f (𝟙 S.X₃) S.f n

lemma tensorCubeLowMixedSection1X_component2 (n : ℤ) :
    tensorCubeLowMixedSection1X S σ n ≫ (tensorCubeLowMixed2 S hS hproj).f n = 0 := by
  have := tensorCubeLowMixed2_target_inclusion_mono S hS hproj
  apply (cancel_mono ((cochainTensorTripleMap S.f S.f (𝟙 S.X₃)).f n)).mp
  rw [Category.assoc, ← HomologicalComplex.comp_f, tensorCubeLowMixed2_inclusion,
    HomologicalComplex.comp_f, tensorCubeLowMixedSection1X_inclusion_assoc,
    ← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) (𝟙 S.X₂) S.g n]
  simp only [tensorCubeLowMixedRawSection1X, cochainTensorTripleDegreeMap_comp,
    tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_third, zero_comp]

lemma tensorCubeLowMixedSection2X_component0 (n : ℤ) :
    tensorCubeLowMixedSection2X S σ n ≫ (tensorCubeLowMixed0 S hS hproj).f n = 0 := by
  have := tensorCubeLowMixed0_target_inclusion_mono S hS hproj
  apply (cancel_mono ((cochainTensorTripleMap (𝟙 S.X₃) S.f S.f).f n)).mp
  rw [Category.assoc, ← HomologicalComplex.comp_f, tensorCubeLowMixed0_inclusion,
    HomologicalComplex.comp_f, tensorCubeLowMixedSection2X_inclusion_assoc,
    ← cochainTensorTripleDegreeMap_eq S.g (𝟙 S.X₂) (𝟙 S.X₂) n]
  simp only [tensorCubeLowMixedRawSection2X, cochainTensorTripleDegreeMap_comp,
    tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_first, zero_comp]

lemma tensorCubeLowMixedSection2X_component1 (n : ℤ) :
    tensorCubeLowMixedSection2X S σ n ≫ (tensorCubeLowMixed1 S hS hproj).f n = 0 := by
  have := tensorCubeLowMixed1_target_inclusion_mono S hS hproj
  apply (cancel_mono ((cochainTensorTripleMap S.f (𝟙 S.X₃) S.f).f n)).mp
  rw [Category.assoc, ← HomologicalComplex.comp_f, tensorCubeLowMixed1_inclusion,
    HomologicalComplex.comp_f, tensorCubeLowMixedSection2X_inclusion_assoc,
    ← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) S.g (𝟙 S.X₂) n]
  simp only [tensorCubeLowMixedRawSection2X, cochainTensorTripleDegreeMap_comp,
    tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_second, zero_comp]

lemma tensorCubeLowMixedSection2X_component2 (n : ℤ) :
    tensorCubeLowMixedSection2X S σ n ≫ (tensorCubeLowMixed2 S hS hproj).f n = 𝟙 _ := by
  have := tensorCubeLowMixed2_target_inclusion_mono S hS hproj
  apply (cancel_mono ((cochainTensorTripleMap S.f S.f (𝟙 S.X₃)).f n)).mp
  rw [Category.assoc, ← HomologicalComplex.comp_f, tensorCubeLowMixed2_inclusion,
    HomologicalComplex.comp_f, tensorCubeLowMixedSection2X_inclusion_assoc,
    id_comp, ← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) (𝟙 S.X₂) S.g n]
  rw [tensorCubeLowMixedRawSection2X, cochainTensorTripleDegreeMap_comp]
  simp only [HomologicalComplex.id_f, comp_id]
  have he : (fun i => cochainSplittingSection S σ i ≫ S.g.f i) =
      (fun i => 𝟙 (S.X₃.X i)) := funext fun i => (σ i).s_g
  rw [he]
  exact cochainTensorTripleDegreeMap_eq S.f S.f (𝟙 S.X₃) n

abbrev tensorCubeLowMixedTarget :=
  cochainTensor (cochainTensor S.X₃ S.X₁) S.X₁ ⊞
    (cochainTensor (cochainTensor S.X₁ S.X₃) S.X₁ ⊞ cochainTensor (cochainTensor S.X₁ S.X₁) S.X₃)

abbrev tensorCubeLowMixedProjection0X (n : ℤ) :
    (tensorCubeLowMixedTarget S).X n ⟶ (cochainTensor (cochainTensor S.X₃ S.X₁) S.X₁).X n :=
  (biprod.fst : tensorCubeLowMixedTarget S ⟶ cochainTensor (cochainTensor S.X₃ S.X₁) S.X₁).f n

abbrev tensorCubeLowMixedProjection1X (n : ℤ) :
    (tensorCubeLowMixedTarget S).X n ⟶ (cochainTensor (cochainTensor S.X₁ S.X₃) S.X₁).X n :=
  ((biprod.snd ≫ biprod.fst) : tensorCubeLowMixedTarget S ⟶
    cochainTensor (cochainTensor S.X₁ S.X₃) S.X₁).f n

abbrev tensorCubeLowMixedProjection2X (n : ℤ) :
    (tensorCubeLowMixedTarget S).X n ⟶ (cochainTensor (cochainTensor S.X₁ S.X₁) S.X₃).X n :=
  ((biprod.snd ≫ biprod.snd) : tensorCubeLowMixedTarget S ⟶
    cochainTensor (cochainTensor S.X₁ S.X₁) S.X₃).f n

@[reassoc]
lemma tensorCubeLowMixedMap_projection0X (n : ℤ) :
    (tensorCubeLowMixedMap S hS hproj).f n ≫ tensorCubeLowMixedProjection0X S n =
      (tensorCubeLowMixed0 S hS hproj).f n := by
  rw [← HomologicalComplex.comp_f, tensorCubeLowMixedMap, biprod.lift_fst]

@[reassoc]
lemma tensorCubeLowMixedMap_projection1X (n : ℤ) :
    (tensorCubeLowMixedMap S hS hproj).f n ≫ tensorCubeLowMixedProjection1X S n =
      (tensorCubeLowMixed1 S hS hproj).f n := by
  rw [← HomologicalComplex.comp_f, tensorCubeLowMixedMap, biprod.lift_snd_assoc, biprod.lift_fst]

@[reassoc]
lemma tensorCubeLowMixedMap_projection2X (n : ℤ) :
    (tensorCubeLowMixedMap S hS hproj).f n ≫ tensorCubeLowMixedProjection2X S n =
      (tensorCubeLowMixed2 S hS hproj).f n := by
  rw [← HomologicalComplex.comp_f, tensorCubeLowMixedMap, biprod.lift_snd_assoc, biprod.lift_snd]

/-- The three graded component lifts form a section of the combined mixed quotient. -/
def tensorCubeLowMixedSectionX (n : ℤ) :
    (tensorCubeLowMixedTarget S).X n ⟶ (tensorCubeFirstLayer S.g).X n :=
  tensorCubeLowMixedProjection0X S n ≫ tensorCubeLowMixedSection0X S σ n +
    tensorCubeLowMixedProjection1X S n ≫ tensorCubeLowMixedSection1X S σ n +
    tensorCubeLowMixedProjection2X S n ≫ tensorCubeLowMixedSection2X S σ n

set_option maxHeartbeats 600000 in
-- All three inverse equations compare evaluated biproduct and iterated kernel models.
lemma tensorCubeLowMixedSectionX_section (n : ℤ) :
    tensorCubeLowMixedSectionX S σ n ≫ (tensorCubeLowMixedMap S hS hproj).f n = 𝟙 _ := by
  apply cochainBiprodDegree_hom_ext (cochainTensor (cochainTensor S.X₃ S.X₁) S.X₁)
    (cochainTensor (cochainTensor S.X₁ S.X₃) S.X₁ ⊞ cochainTensor (cochainTensor S.X₁ S.X₁) S.X₃) n
  · rw [Category.assoc, tensorCubeLowMixedMap_projection0X, id_comp]
    exact section_sum0 _ _ _ _ _ _ _
      (tensorCubeLowMixedSection0X_component0 S σ hS hproj n)
      (tensorCubeLowMixedSection1X_component0 S σ hS hproj n)
      (tensorCubeLowMixedSection2X_component0 S σ hS hproj n)
  · apply cochainBiprodDegree_hom_ext (cochainTensor (cochainTensor S.X₁ S.X₃) S.X₁)
      (cochainTensor (cochainTensor S.X₁ S.X₁) S.X₃) n
    · rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f,
        tensorCubeLowMixedMap_projection1X]
      simp only [id_comp]
      exact section_sum1 _ _ _ _ _ _ _
        (tensorCubeLowMixedSection0X_component1 S σ hS hproj n)
        (tensorCubeLowMixedSection1X_component1 S σ hS hproj n)
        (tensorCubeLowMixedSection2X_component1 S σ hS hproj n)
    · rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f,
        tensorCubeLowMixedMap_projection2X]
      simp only [id_comp]
      exact section_sum2 _ _ _ _ _ _ _
        (tensorCubeLowMixedSection0X_component2 S σ hS hproj n)
        (tensorCubeLowMixedSection1X_component2 S σ hS hproj n)
        (tensorCubeLowMixedSection2X_component2 S σ hS hproj n)

omit σ in
lemma tensorCubeLowMixedMap_epi : Epi (tensorCubeLowMixedMap S hS hproj) := by
  let σ := cochainDegreewiseSplittingOfProjective S hS hproj
  apply HomologicalComplex.epi_of_epi_f
  intro n
  exact epi_of_epi_fac (tensorCubeLowMixedSectionX_section S σ hS hproj n)

end Adams
end SerrePositivity
