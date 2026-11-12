module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SmallHomComparison
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.AccessibleModelMapping

/-! # Accessible small-Hom mapping tests at a common cardinal

Only the fixed small family of source arrows is bounded. Its actual
cosimplicial objects are represented in ShrinkHoms C. Their small-Hom
tests and the specified target replacement are accessible together.
The original Hom and small-object universes remain independent.
-/

@[expose] public section
universe w t v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite

namespace SerrePositivity.HomotopyFunctionComplex.SmallHomComparison
variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]

omit [ModelCategory C] in
lemma hom_isCardinalAccessible (Q : C ⥤ SimplexCategory ⥤ C) (R : C ⥤ C) (X : Cᵒᵖ)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [R.IsCardinalAccessible κ]
    [∀ n, IsCardinalPresentable ((SmallHomRealization.frame (Q.obj X.unop)).obj n) κ] :
    ((hom Q R).obj X).IsCardinalAccessible κ := by
  have : (changeHom (C := C)).IsCardinalAccessible κ :=
    { preservesColimitOfShape := by intros; infer_instance }
  have := cosimplicialHom_isCardinalAccessible (SmallHomRealization.frame (Q.obj X.unop)) κ
  exact inferInstanceAs (((R ⋙ changeHom (C := C)) ⋙
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (SmallHomRealization.frame (Q.obj X.unop))).IsCardinalAccessible κ)

lemma exists_accessible_mapping_tests
    (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
    {ι : Type t} [Small.{w} ι] (s : ι → Arrow C) :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      ∃ d : Smith.AccessibleModelFactorizations C κ,
        IsCardinalAccessibleCategory (Smith.arrowProperty (weakEquivalences C)).FullSubcategory κ ∧
        (Smith.arrowInclusion (weakEquivalences C)).IsCardinalAccessible κ ∧
        (∀ i, ((chosenHom d.cofibrationData d.fibrationData).obj
            (op (s i).left)).IsCardinalAccessible κ ∧
          ((chosenHom d.cofibrationData d.fibrationData).obj
            (op (s i).right)).IsCardinalAccessible κ) ∧
        (MappingTests.family (chosenHom d.cofibrationData d.fibrationData) s).IsCardinalAccessible
          κ := by
  have := SmallHomModel.locallyPresentable.{w} C
  obtain ⟨κ₀, h₀, d₀, hW, hι⟩ := Smith.exists_accessible_model_and_weakEquivalences I J
  let Q := (Reedy.cosimplicialResolutionFamily d₀.cofibrationData).obj
  let a : Sum ι ι → C := Sum.elim (fun i => (s i).left) (fun i => (s i).right)
  obtain ⟨μ, hμ, hA⟩ := exists_common_degree_presentability
    (fun i => SmallHomRealization.frame (Q.obj (a i)))
  obtain ⟨κ, hκ, h₀κ, hμκ⟩ := Cardinal.SharplyLT.exists_of_pair κ₀ μ
  let d := d₀.atLarger κ h₀κ.le
  have hp : ∀ i n, IsCardinalPresentable
      ((SmallHomRealization.frame (Q.obj (a i))).obj n) κ := by
    intro i n
    have := hA i n
    exact isCardinalPresentable_of_le _ hμκ.le
  have hR : (fibrantTarget d.fibrationData).IsCardinalAccessible κ := d.R_isCardinalAccessible
  have hl : ∀ i, ((chosenHom d.cofibrationData d.fibrationData).obj
      (op (s i).left)).IsCardinalAccessible κ := by
    intro i
    have : ∀ n, IsCardinalPresentable
        ((SmallHomRealization.frame
          ((Reedy.cosimplicialResolutionFamily d.cofibrationData).obj.obj (s i).left)).obj n) κ :=
      hp (.inl i)
    exact hom_isCardinalAccessible (Reedy.cosimplicialResolutionFamily d.cofibrationData).obj
      (fibrantTarget d.fibrationData) (op (s i).left) κ
  have hr : ∀ i, ((chosenHom d.cofibrationData d.fibrationData).obj
      (op (s i).right)).IsCardinalAccessible κ := by
    intro i
    have : ∀ n, IsCardinalPresentable
        ((SmallHomRealization.frame
          ((Reedy.cosimplicialResolutionFamily d.cofibrationData).obj.obj (s i).right)).obj n) κ :=
      hp (.inr i)
    exact hom_isCardinalAccessible (Reedy.cosimplicialResolutionFamily d.cofibrationData).obj
      (fibrantTarget d.fibrationData) (op (s i).right) κ
  exact ⟨κ, hκ, d, h₀κ.isCardinalAccessibleCategory _,
    Functor.isCardinalAccessible_of_le _ h₀κ.le, fun i => ⟨hl i, hr i⟩,
    MappingTests.family_isCardinalAccessible _ s κ⟩

end SerrePositivity.HomotopyFunctionComplex.SmallHomComparison
