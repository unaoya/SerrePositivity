module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Accessible
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ChosenResolutionHom
public import SerrePositivity.HomotopicalAlgebra.Smith.WeakEquivalencesAccessible

/-! # A common accessibility cardinal for model replacements and fixed mapping tests

Only the original combinatorial model and a small family of actual arrows
are input. Specified source factorizations, their replacements, the original
weak-equivalence subcategory, and all mapping tests share an output cardinal.
Accessibility of the entire source resolution functor is a separate claim.
-/

@[expose] public section
universe w t v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C]

namespace AccessibleModelMapping
variable {κ : Cardinal.{w}} [Fact κ.IsRegular] (d : Smith.AccessibleModelFactorizations C κ)

abbrev hom : Cᵒᵖ ⥤ C ⥤ SSet.{v} := chosenResolutionHom d.cofibrationData d.fibrationData

lemma hom_isCardinalAccessible (X : C)
    [∀ n, IsCardinalPresentable
      (((Reedy.cosimplicialResolutionFamily d.cofibrationData).obj.obj X).obj n) κ] :
    ((hom d).obj (op X)).IsCardinalAccessible κ := by
  have : (fibrantTarget d.fibrationData).IsCardinalAccessible κ := d.R_isCardinalAccessible
  exact resolutionHom_isCardinalAccessible _ _ (op X) κ

end AccessibleModelMapping

variable [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

include I J in
/-- The actual two source resolutions and target replacement used by all
fixed mapping tests work at one common cardinal with A0 and A1. -/
lemma exists_accessible_model_mapping_tests {ι : Type t} [Small.{w} ι] (s : ι → Arrow C) :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      ∃ d : Smith.AccessibleModelFactorizations C κ,
        IsCardinalAccessibleCategory (Smith.arrowProperty (weakEquivalences C)).FullSubcategory κ ∧
        (Smith.arrowInclusion (weakEquivalences C)).IsCardinalAccessible κ ∧
        (∀ i, ((AccessibleModelMapping.hom d).obj (op (s i).left)).IsCardinalAccessible κ ∧
          ((AccessibleModelMapping.hom d).obj (op (s i).right)).IsCardinalAccessible κ) ∧
        (MappingTests.family (AccessibleModelMapping.hom d) s).IsCardinalAccessible κ := by
  obtain ⟨κ₀, h₀, d₀, hW, hι⟩ := Smith.exists_accessible_model_and_weakEquivalences I J
  let Q := (Reedy.cosimplicialResolutionFamily d₀.cofibrationData).obj
  let a : Sum ι ι → C := Sum.elim (fun i ↦ (s i).left) (fun i ↦ (s i).right)
  obtain ⟨μ, hμ, hA⟩ := exists_common_degree_presentability (fun i ↦ Q.obj (a i))
  obtain ⟨κ, hκ, h₀κ, hμκ⟩ := Cardinal.SharplyLT.exists_of_pair κ₀ μ
  let d := d₀.atLarger κ h₀κ.le
  have hp : ∀ i n, IsCardinalPresentable ((Q.obj (a i)).obj n) κ := by
    intro i n
    have := hA i n
    exact isCardinalPresentable_of_le _ hμκ.le
  have hl : ∀ i, ((AccessibleModelMapping.hom d).obj (op (s i).left)).IsCardinalAccessible κ := by
    intro i
    have : ∀ n, IsCardinalPresentable
        (((Reedy.cosimplicialResolutionFamily d.cofibrationData).obj.obj (s i).left).obj n) κ :=
      hp (.inl i)
    exact AccessibleModelMapping.hom_isCardinalAccessible d (s i).left
  have hr : ∀ i, ((AccessibleModelMapping.hom d).obj (op (s i).right)).IsCardinalAccessible κ := by
    intro i
    have : ∀ n, IsCardinalPresentable
        (((Reedy.cosimplicialResolutionFamily d.cofibrationData).obj.obj (s i).right).obj n) κ :=
      hp (.inr i)
    exact AccessibleModelMapping.hom_isCardinalAccessible d (s i).right
  exact ⟨κ, hκ, d, h₀κ.isCardinalAccessibleCategory _,
    Functor.isCardinalAccessible_of_le _ h₀κ.le, fun i ↦ ⟨hl i, hr i⟩,
    MappingTests.family_isCardinalAccessible _ s κ⟩

end SerrePositivity.HomotopyFunctionComplex
