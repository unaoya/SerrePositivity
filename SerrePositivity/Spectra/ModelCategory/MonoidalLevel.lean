module

public import SerrePositivity.Spectra.ModelCategory.LevelFromGenerators
public import SerrePositivity.Spectra.ModelCategory.FreeLevelCofibrations

/-! # Level models with cofibrant suspension coordinate

For a monoidal model category with cofibrant unit and K, the free-level
trivial-cofibration test is proved by the induction calculation. Together with
a presentability bound on source generators, this gives the level model without
any separate image-smallness, cell-acyclicity or evaluated-generator assumption.
-/

@[expose] public section
universe w u v
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra CategoryTheory.MonoidalCategory
open SerrePositivity.GeneralSymmetricSpectrum SerrePositivity.ModelGeneration
open SerrePositivity.Quillen

namespace SerrePositivity.SpectrumLevelModel
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [HasColimitsOfSize.{w, w} C] [ModelCategory C]
  [IsQuillenBifunctor (curriedTensor C)] [IsCofibrant (𝟙_ C)] (K : C) [IsCofibrant K]

omit [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{w, w} C] in
lemma evaluatedFree_generators (J : MorphismProperty C) (hJ : J ≤ trivialCofibrations C)
    (n m : ℕ) : J.strictMap (freeAt (K := K) n ⋙ evaluation m) ≤ trivialCofibrations C := by
  intro X Y f hf
  cases hf with
  | map hf =>
    obtain ⟨_, _⟩ := (mem_trivialCofibrations_iff _).1 (hJ _ hf)
    exact evaluatedFree_trivialCofibration K _ n m

variable [LocallySmall.{w} (GeneralSymmetricSpectrum C K)]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (hI : ∀ {A B : C} (i : A ⟶ B), I i → IsCardinalPresentable A κ)
  (hJ : ∀ {A B : C} (i : A ⟶ B), J i → IsCardinalPresentable A κ)

@[instance_reducible]
def levelModelCategoryOfMonoidalGenerators : ModelCategory (GeneralSymmetricSpectrum C K) :=
  levelModelCategoryOfGenerators K I J κ hI hJ
    (evaluatedFree_generators K J
      (J.le_llp_rlp.trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.trivialCofibrations_eq_generated I J).symm.le))

lemma levelModelCategoryOfMonoidalGenerators_generated :
    let := levelModelCategoryOfMonoidalGenerators K I J κ hI hJ
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} (levelGenerators K I) (levelGenerators K J) :=
  levelModelCategoryOfGenerators_generated K I J κ hI hJ
    (evaluatedFree_generators K J
      (J.le_llp_rlp.trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.trivialCofibrations_eq_generated I J).symm.le))

lemma levelModelCategoryOfMonoidalGenerators_weakEquivalences :
    @weakEquivalences (GeneralSymmetricSpectrum C K) _
        (levelModelCategoryOfMonoidalGenerators K I J κ hI hJ).categoryWithWeakEquivalences =
      levelProperty K (weakEquivalences C) := rfl

lemma levelModelCategoryOfMonoidalGenerators_fibrations :
    @fibrations (GeneralSymmetricSpectrum C K) _
        (levelModelCategoryOfMonoidalGenerators K I J κ hI hJ).categoryWithFibrations =
      levelProperty K (fibrations C) := rfl
end SerrePositivity.SpectrumLevelModel
