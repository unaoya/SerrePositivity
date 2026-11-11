module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.AccessibleModelMapping
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.AccessibleResolution

/-! # A common cardinal for actual resolutions and fixed derived mapping tests -/

@[expose] public section
universe w t v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]

lemma cosimplicialResolutionFamily_isAccessible
    (source : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    [source.Z.IsAccessible.{w}] :
    (Reedy.cosimplicialResolutionFamily source).obj.IsAccessible.{w} :=
  Reedy.cofibrantResolutionFamily_isAccessible.{w} Reedy.simplex
    (fun _ _ h ↦ SimplexCategory.ext h) (fun n ↦ ⟨SimplexCategory.mk n, rfl⟩) source

lemma simplicialResolutionFamily_isAccessible
    (source : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    [source.Z.IsAccessible.{w}] : (Reedy.simplicialResolutionFamily source).obj.IsAccessible.{w} :=
  Reedy.fibrantResolutionFamily_isAccessible.{w} Reedy.simplexOp
    (fun _ _ h ↦ Opposite.unop_injective (SimplexCategory.ext h))
    (fun n ↦ ⟨op (SimplexCategory.mk n), rfl⟩) source

variable (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

include I J in
/-- F3's common cardinal includes the actual source-variable resolution
functors, both specified model factorizations and replacements, original W,
and the RMap evaluations and precomposition tests for the fixed small family. -/
lemma exists_accessible_resolutions_and_mapping_tests {ι : Type t} [Small.{w} ι]
    (s : ι → Arrow C) :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      ∃ d : Smith.AccessibleModelFactorizations C κ,
        (Reedy.cosimplicialResolutionFamily d.cofibrationData).obj.IsCardinalAccessible κ ∧
        (Reedy.simplicialResolutionFamily d.fibrationData).obj.IsCardinalAccessible κ ∧
        IsCardinalAccessibleCategory (Smith.arrowProperty (weakEquivalences C)).FullSubcategory κ ∧
        (Smith.arrowInclusion (weakEquivalences C)).IsCardinalAccessible κ ∧
        (∀ i, ((AccessibleModelMapping.hom d).obj (op (s i).left)).IsCardinalAccessible κ ∧
          ((AccessibleModelMapping.hom d).obj (op (s i).right)).IsCardinalAccessible κ) ∧
        (MappingTests.family (AccessibleModelMapping.hom d) s).IsCardinalAccessible κ := by
  obtain ⟨κ₀, h₀, d₀, hW, hι, hends, htests⟩ := exists_accessible_model_mapping_tests I J s
  have := d₀.cofibrationAccessible
  have := d₀.fibrationAccessible
  have : d₀.cofibrationData.Z.IsAccessible.{w} :=
    Functor.isAccessible_of_isCardinalAccessible _ κ₀
  have : d₀.fibrationData.Z.IsAccessible.{w} :=
    Functor.isAccessible_of_isCardinalAccessible _ κ₀
  have := cosimplicialResolutionFamily_isAccessible d₀.cofibrationData
  have := simplicialResolutionFamily_isAccessible d₀.fibrationData
  obtain ⟨μQ, hμQ, hQ⟩ := Functor.IsAccessible.exists_cardinal
    (Reedy.cosimplicialResolutionFamily d₀.cofibrationData).obj
  obtain ⟨μR, hμR, hR⟩ := Functor.IsAccessible.exists_cardinal
    (Reedy.simplicialResolutionFamily d₀.fibrationData).obj
  obtain ⟨μ, hμ, hQμ, hRμ⟩ := Cardinal.SharplyLT.exists_of_pair μQ μR
  obtain ⟨κ, hκ, h₀κ, hμκ⟩ := Cardinal.SharplyLT.exists_of_pair κ₀ μ
  let d := d₀.atLarger κ h₀κ.le
  refine ⟨κ, hκ, d,
    Functor.isCardinalAccessible_of_le (Reedy.cosimplicialResolutionFamily d₀.cofibrationData).obj
      (hQμ.le.trans hμκ.le),
    Functor.isCardinalAccessible_of_le (Reedy.simplicialResolutionFamily d₀.fibrationData).obj
      (hRμ.le.trans hμκ.le),
    h₀κ.isCardinalAccessibleCategory _, Functor.isCardinalAccessible_of_le _ h₀κ.le,
    ?_, Functor.isCardinalAccessible_of_le (MappingTests.family (AccessibleModelMapping.hom d₀) s)
      h₀κ.le⟩
  intro i
  have := (hends i).1
  have := (hends i).2
  exact ⟨Functor.isCardinalAccessible_of_le ((AccessibleModelMapping.hom d₀).obj (op (s i).left))
      h₀κ.le,
    Functor.isCardinalAccessible_of_le ((AccessibleModelMapping.hom d₀).obj (op (s i).right))
      h₀κ.le⟩

end SerrePositivity.HomotopyFunctionComplex
