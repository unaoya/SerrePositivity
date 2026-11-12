module

public import SerrePositivity.Spectra.ModelCategory.LevelClasses
public import SerrePositivity.Spectra.General.Limits
public import SerrePositivity.HomotopicalAlgebra.Transfer.Recognition

/-! # Recognition of the level model structure

The right lifting class computation is proved in LevelClasses. Here we apply
Mathlib's small object argument and the shared recognition theorem to the
chosen level classes. The image smallness and image J-cell acyclicity inputs
remain explicit: this theorem does not assert that they hold for every C,K.
-/

@[expose] public section
universe w u v
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.GeneralSymmetricSpectrum SerrePositivity.ModelGeneration

namespace SerrePositivity.SpectrumLevelModel
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] (K : C)

instance levelProperty_twoOutOfThree (P : MorphismProperty C) [P.HasTwoOutOfThreeProperty] :
    (levelProperty K P).HasTwoOutOfThreeProperty where
  comp_mem f g hf hg n := P.comp_mem (levelMap f n) (levelMap g n) (hf n) (hg n)
  of_postcomp f g hg hfg n := P.of_postcomp (levelMap f n) (levelMap g n) (hg n) (hfg n)
  of_precomp f g hf hfg n := P.of_precomp (levelMap f n) (levelMap g n) (hf n) (hfg n)

instance levelProperty_retracts (P : MorphismProperty C) [P.IsStableUnderRetracts] :
    (levelProperty K P).IsStableUnderRetracts where
  of_retract h hg n := MorphismProperty.of_retract (h.map (evaluation n)) (hg n)

/-- Fibrations detected by every evaluation functor. -/
@[instance_reducible]
def levelFibrations [CategoryWithFibrations C] :
    CategoryWithFibrations (GeneralSymmetricSpectrum C K) where
  fibrations := levelProperty K (fibrations C)

/-- Weak equivalences detected by every evaluation functor. -/
@[instance_reducible]
def levelWeakEquivalences [CategoryWithWeakEquivalences C] :
    CategoryWithWeakEquivalences (GeneralSymmetricSpectrum C K) where
  weakEquivalences := levelProperty K (weakEquivalences C)

/-- Cofibrations defined by lifting against level trivial fibrations. -/
@[instance_reducible]
def levelCofibrations (I : MorphismProperty C) :
    CategoryWithCofibrations (GeneralSymmetricSpectrum C K) where
  cofibrations := (levelGenerators K I).rlp.llp

variable [ModelCategory C] [HasLimitsOfSize.{0, 0} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [(levelGenerators K I).HasSmallObjectArgument.{w}]
  [(levelGenerators K J).HasSmallObjectArgument.{w}]

/-- Build the level model category from smallness and cell acyclicity. -/
@[instance_reducible]
def levelModelCategory
    (hacyclic : MorphismProperty.transfiniteCompositions.{w}
      (MorphismProperty.coproducts.{w} (levelGenerators K J)).pushouts ≤
        levelProperty K (weakEquivalences C)) :
    ModelCategory (GeneralSymmetricSpectrum C K) := by
  letI := levelFibrations K
  letI := levelWeakEquivalences K
  letI := levelCofibrations K I
  let : HasFiniteLimits (GeneralSymmetricSpectrum C K) := { out := fun D _ _ ↦ inferInstance }
  let : HasFiniteColimits (GeneralSymmetricSpectrum C K) := { out := fun D _ _ ↦ inferInstance }
  have : (weakEquivalences (GeneralSymmetricSpectrum C K)).HasTwoOutOfThreeProperty :=
    inferInstanceAs ((levelProperty K (weakEquivalences C)).HasTwoOutOfThreeProperty)
  have : (weakEquivalences (GeneralSymmetricSpectrum C K)).IsStableUnderRetracts :=
    inferInstanceAs ((levelProperty K (weakEquivalences C)).IsStableUnderRetracts)
  have hI : (levelGenerators K I).rlp = trivialFibrations (GeneralSymmetricSpectrum C K) := by
    rw [generatingCofibrations_rlp K I J]
    change levelProperty K (fibrations C ⊓ weakEquivalences C) = _
    exact levelProperty_inf K _ _
  have hJ : (levelGenerators K J).rlp = fibrations (GeneralSymmetricSpectrum C K) :=
    generatingTrivialCofibrations_rlp K I J
  exact modelCategoryOfRecognition (levelGenerators K I) (levelGenerators K J) hI hJ rfl
    (generatedLeft_le_of_cells_le _ _ hacyclic)

lemma levelModelCategory_weakEquivalences (hacyclic) :
    @weakEquivalences (GeneralSymmetricSpectrum C K) _
        (levelModelCategory K I J hacyclic).categoryWithWeakEquivalences =
      levelProperty K (weakEquivalences C) := rfl

lemma levelModelCategory_fibrations (hacyclic) :
    @fibrations (GeneralSymmetricSpectrum C K) _
        (levelModelCategory K I J hacyclic).categoryWithFibrations =
      levelProperty K (fibrations C) := rfl
section Consequences
variable (hacyclic : MorphismProperty.transfiniteCompositions.{w}
    (MorphismProperty.coproducts.{w} (levelGenerators K J)).pushouts ≤
      levelProperty K (weakEquivalences C))

lemma levelModelCategory_generated :
    let := levelModelCategory K I J hacyclic
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} (levelGenerators K I) (levelGenerators K J) := by
  let := levelModelCategory K I J hacyclic
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · rw [generatingCofibrations_rlp K I J]
    exact levelProperty_inf K _ _
  · exact generatingTrivialCofibrations_rlp K I J

lemma evaluation_isRightQuillen (n : ℕ) :
    let := levelModelCategory K I J hacyclic
    SerrePositivity.Quillen.IsRightQuillen (evaluation (K := K) n) := by
  let := levelModelCategory K I J hacyclic
  exact ⟨fun _ _ _ hf ↦ hf n, fun _ _ _ hf ↦ ⟨hf.1 n, hf.2 n⟩⟩

lemma freeAt_isLeftQuillen (n : ℕ) :
    let := levelModelCategory K I J hacyclic
    SerrePositivity.Quillen.IsLeftQuillen (freeAt (K := K) n) := by
  let := levelModelCategory K I J hacyclic
  have := evaluation_isRightQuillen K I J hacyclic n
  exact SerrePositivity.Quillen.isLeftQuillen_of_isRightQuillen (freeAtAdjunction n)

lemma levelFunctorialFactorizations :
    let := levelModelCategory K I J hacyclic
    (cofibrations (GeneralSymmetricSpectrum C K)).HasFunctorialFactorization
        (trivialFibrations (GeneralSymmetricSpectrum C K)) ∧
      (trivialCofibrations (GeneralSymmetricSpectrum C K)).HasFunctorialFactorization
        (fibrations (GeneralSymmetricSpectrum C K)) := by
  let := levelModelCategory K I J hacyclic
  have := levelModelCategory_generated K I J hacyclic
  exact ⟨_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_cofibration_trivialFibration
      (levelGenerators K I) (levelGenerators K J),
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_trivialCofibration_fibration
      (levelGenerators K I) (levelGenerators K J)⟩
end Consequences

end SerrePositivity.SpectrumLevelModel
