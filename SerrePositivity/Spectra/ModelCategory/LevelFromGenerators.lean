module

public import SerrePositivity.Spectra.ModelCategory.LevelAcyclicity
public import SerrePositivity.Spectra.ModelCategory.LevelSmallness

/-! # Constructing the level model from generator data

The inputs are a presentability bound on source generator domains and the
trivial-cofibration test on evaluated free generators. Both the image SOA and
cell acyclicity required by level recognition are proved in this construction.
Concrete categories still have to provide these algebraic/topological inputs.
-/

@[expose] public section
universe w u v
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.GeneralSymmetricSpectrum SerrePositivity.ModelGeneration

namespace SerrePositivity.SpectrumLevelModel
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [HasColimitsOfSize.{w, w} C] [ModelCategory C] (K : C)
  [LocallySmall.{w} (GeneralSymmetricSpectrum C K)]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (hI : ∀ {A B : C} (i : A ⟶ B), I i → IsCardinalPresentable A κ)
  (hJ : ∀ {A B : C} (i : A ⟶ B), J i → IsCardinalPresentable A κ)
  (heval : ∀ n m : ℕ, J.strictMap (freeAt (K := K) n ⋙ evaluation m) ≤
    trivialCofibrations C)

/-- The level model structure, with no image-SOA or cell-acyclicity assumption. -/
@[instance_reducible]
def levelModelCategoryOfGenerators : ModelCategory (GeneralSymmetricSpectrum C K) := by
  have : I.IsSmall.{w} := isSmall_of_smallObjectArgument I
  have : J.IsSmall.{w} := isSmall_of_smallObjectArgument J
  have := levelGenerators_smallObjectArgument K I κ hI
  have := levelGenerators_smallObjectArgument K J κ hJ
  exact levelModelCategory K I J (levelCells_acyclic_of_evaluated_generators K J heval)

lemma levelModelCategoryOfGenerators_weakEquivalences :
    @weakEquivalences (GeneralSymmetricSpectrum C K) _
        (levelModelCategoryOfGenerators K I J κ hI hJ heval).categoryWithWeakEquivalences =
      levelProperty K (weakEquivalences C) := rfl

lemma levelModelCategoryOfGenerators_fibrations :
    @fibrations (GeneralSymmetricSpectrum C K) _
        (levelModelCategoryOfGenerators K I J κ hI hJ heval).categoryWithFibrations =
      levelProperty K (fibrations C) := rfl
lemma levelModelCategoryOfGenerators_generated :
    let := levelModelCategoryOfGenerators K I J κ hI hJ heval
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} (levelGenerators K I) (levelGenerators K J) := by
  have : I.IsSmall.{w} := isSmall_of_smallObjectArgument I
  have : J.IsSmall.{w} := isSmall_of_smallObjectArgument J
  have := levelGenerators_smallObjectArgument K I κ hI
  have := levelGenerators_smallObjectArgument K J κ hJ
  exact levelModelCategory_generated K I J (levelCells_acyclic_of_evaluated_generators K J heval)

end SerrePositivity.SpectrumLevelModel
