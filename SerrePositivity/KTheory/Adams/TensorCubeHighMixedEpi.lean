module

public import SerrePositivity.KTheory.Adams.TensorCubeHighMixedSections

/-! # A degreewise section of the high mixed quotient -/

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
