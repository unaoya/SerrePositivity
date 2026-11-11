module

public import SerrePositivity.HomotopicalAlgebra.Monoidal.ManyObjectTransfer
public import SerrePositivity.HomotopicalAlgebra.Transfer.EvaluationSmallness

/-! # Many-object model transfer from presentable source generators

No free-image small-object hypothesis or cell-acyclicity hypothesis is assumed.
The concrete theory supplies a common cardinal bound, evaluation colimit
preservation, and the natural free/evaluation tensor formula.
-/

@[expose] public section
universe w t u v u' v'
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.Quillen SerrePositivity.ModelGeneration
namespace SerrePositivity.ManyObjectModelTransfer
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {ι : Type t} [Small.{w} ι]
  [MonoidalCategory C] [BraidedCategory C] [ModelCategory C] [HasMonoidAxiom.{w} C]
  [HasFiniteLimits D] [HasFiniteColimits D] [HasColimitsOfSize.{w, w} D] [LocallySmall.{w} D]
  (L : ι → C ⥤ D) (R : ι → D ⥤ C) (adj : ∀ i, L i ⊣ R i)
  [∀ i, PreservesColimitsOfSize.{w, w} (R i)]
  [∀ i, PreservesColimitsOfShape WalkingSpan (R i)]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (hI : ∀ {A B : C} (f : A ⟶ B), I f → IsCardinalPresentable A κ)
  (hJ : ∀ {A B : C} (f : A ⟶ B), J f → IsCardinalPresentable A κ)
  (H : ι → ι → C) (e : ∀ i j, L i ⋙ R j ≅ tensorLeft (H i j))

/-- Many-object transfer with both image smallness and acyclicity proved. -/
@[instance_reducible]
def modelCategoryOfPresentableGenerators : ModelCategory D := by
  have : I.IsSmall.{w} := EvaluationFamily.isSmall_of_smallObjectArgument I
  have : J.IsSmall.{w} := EvaluationFamily.isSmall_of_smallObjectArgument J
  have := EvaluationFamily.generators_smallObjectArgument L R adj I κ hI
  have := EvaluationFamily.generators_smallObjectArgument L R adj J κ hJ
  exact modelCategoryOfTensorFormula L R I J adj H e

lemma modelCategoryOfPresentableGenerators_weakEquivalences :
    @weakEquivalences D _
        (modelCategoryOfPresentableGenerators L R adj I J κ hI hJ H e).categoryWithWeakEquivalences
          =
      EvaluationFamily.detected R (weakEquivalences C) := rfl

lemma modelCategoryOfPresentableGenerators_fibrations :
    @fibrations D _
        (modelCategoryOfPresentableGenerators L R adj I J κ hI hJ H e).categoryWithFibrations =
      EvaluationFamily.detected R (fibrations C) := rfl

lemma modelCategoryOfPresentableGenerators_generated :
    let := modelCategoryOfPresentableGenerators L R adj I J κ hI hJ H e
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w}
      (EvaluationFamily.generators L I) (EvaluationFamily.generators L J) := by
  have : I.IsSmall.{w} := EvaluationFamily.isSmall_of_smallObjectArgument I
  have : J.IsSmall.{w} := EvaluationFamily.isSmall_of_smallObjectArgument J
  have := EvaluationFamily.generators_smallObjectArgument L R adj I κ hI
  have := EvaluationFamily.generators_smallObjectArgument L R adj J κ hJ
  exact modelCategory_generated L R I J adj (freeGenerators_tensor_images L R J H e)

end SerrePositivity.ManyObjectModelTransfer
