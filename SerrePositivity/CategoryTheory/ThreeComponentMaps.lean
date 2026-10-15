module
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Component formulas for three summands -/
@[expose] public section
namespace SerrePositivity
open CategoryTheory Category Limits Preadditive

lemma section_sum0 {C : Type*} [Category C] [Preadditive C]
    {W K Y₀ Y₁ Y₂ : C} (p₀ : W ⟶ Y₀) (p₁ : W ⟶ Y₁) (p₂ : W ⟶ Y₂)
    (d₀ : Y₀ ⟶ K) (d₁ : Y₁ ⟶ K) (d₂ : Y₂ ⟶ K) (m : K ⟶ Y₀)
    (h₀ : d₀ ≫ m = 𝟙 _) (h₁ : d₁ ≫ m = 0) (h₂ : d₂ ≫ m = 0) :
    (p₀ ≫ d₀ + p₁ ≫ d₁ + p₂ ≫ d₂) ≫ m = p₀ := by
  rw [add_comp, add_comp, Category.assoc, Category.assoc, Category.assoc, h₀, h₁, h₂]
  simp only [comp_id, comp_zero, add_zero]

lemma section_sum1 {C : Type*} [Category C] [Preadditive C]
    {W K Y₀ Y₁ Y₂ : C} (p₀ : W ⟶ Y₀) (p₁ : W ⟶ Y₁) (p₂ : W ⟶ Y₂)
    (d₀ : Y₀ ⟶ K) (d₁ : Y₁ ⟶ K) (d₂ : Y₂ ⟶ K) (m : K ⟶ Y₁)
    (h₀ : d₀ ≫ m = 0) (h₁ : d₁ ≫ m = 𝟙 _) (h₂ : d₂ ≫ m = 0) :
    (p₀ ≫ d₀ + p₁ ≫ d₁ + p₂ ≫ d₂) ≫ m = p₁ := by
  rw [add_comp, add_comp, Category.assoc, Category.assoc, Category.assoc, h₀, h₁, h₂]
  simp only [comp_id, comp_zero, zero_add, add_zero]

lemma section_sum2 {C : Type*} [Category C] [Preadditive C]
    {W K Y₀ Y₁ Y₂ : C} (p₀ : W ⟶ Y₀) (p₁ : W ⟶ Y₁) (p₂ : W ⟶ Y₂)
    (d₀ : Y₀ ⟶ K) (d₁ : Y₁ ⟶ K) (d₂ : Y₂ ⟶ K) (m : K ⟶ Y₂)
    (h₀ : d₀ ≫ m = 0) (h₁ : d₁ ≫ m = 0) (h₂ : d₂ ≫ m = 𝟙 _) :
    (p₀ ≫ d₀ + p₁ ≫ d₁ + p₂ ≫ d₂) ≫ m = p₂ := by
  rw [add_comp, add_comp, Category.assoc, Category.assoc, Category.assoc, h₀, h₁, h₂]
  simp only [comp_id, comp_zero, zero_add, add_zero]

lemma three_components_rotation {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasBinaryBiproducts C] {K U₀ U₁ U₂ : C} (τ : K ⟶ K)
    (m₀ : K ⟶ U₀) (m₁ : K ⟶ U₁) (m₂ : K ⟶ U₂)
    (r₀ : U₀ ⟶ U₁) (r₁ : U₁ ⟶ U₂) (r₂ : U₂ ⟶ U₀)
    (h₀ : τ ≫ m₀ = m₂ ≫ r₂) (h₁ : τ ≫ m₁ = m₀ ≫ r₀)
    (h₂ : τ ≫ m₂ = m₁ ≫ r₁) :
    τ ≫ biprod.lift m₀ (biprod.lift m₁ m₂) =
      biprod.lift m₀ (biprod.lift m₁ m₂) ≫
        biprod.lift (biprod.snd ≫ biprod.snd ≫ r₂)
          (biprod.lift (biprod.fst ≫ r₀) (biprod.snd ≫ biprod.fst ≫ r₁)) := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd_assoc, h₀]
  · apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, biprod.lift_fst_assoc,
        biprod.lift_snd, h₁]
    · simp only [Category.assoc, biprod.lift_fst_assoc,
        biprod.lift_snd, biprod.lift_snd_assoc, h₂]

end SerrePositivity
