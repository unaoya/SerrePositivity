module

public import SerrePositivity.Spectra.ModelCategory.SimplicialMonoidal
public import SerrePositivity.Spectra.ModelCategory.MonoidalLevel
public import SerrePositivity.Spectra.General.SimplicialComparison

/-! # Level model on the existing circle-based simplicial symmetric spectra

The source model is an explicit input with its actual mono/Kan class
equalities. All pointed generator, smallness and evaluated-free acyclicity
inputs are proved; no model existence theorem is postulated here.
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.ModelGeneration SerrePositivity.Quillen
open SerrePositivity.SpectrumLevelModel
namespace SerrePositivity.SimplicialModelInputs
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

abbrev simplicialLevelI : MorphismProperty SymmetricSpectrum.{u} :=
  levelGenerators PointedSimplicialSet.circle.{u} pointedI.{u}

abbrev simplicialLevelJ : MorphismProperty SymmetricSpectrum.{u} :=
  levelGenerators PointedSimplicialSet.circle.{u} pointedJ.{u}

variable [ModelCategory SSet.{u}]
  (hCof : cofibrations SSet.{u} = MorphismProperty.monomorphisms SSet.{u})
  (hFib : fibrations SSet.{u} = SSet.modelCategoryQuillen.J.{u}.rlp)

/-- A locally selected level model on the original `SymmetricSpectrum` type. -/
@[instance_reducible]
def simplicialLevelModelCategory : ModelCategory SymmetricSpectrum.{u} := by
  let : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} pointedI.{u} pointedJ.{u} :=
    pointedSimplicial_cofibrantlyGenerated hCof hFib
  let : MonoidalModelCategory PointedSimplicialSet.{u} :=
    pointedSimplicial_monoidalModel hCof hFib
  let : IsCofibrant (𝟙_ PointedSimplicialSet.{u}) := pointedSimplicial_isCofibrant hCof _
  let : IsCofibrant PointedSimplicialSet.circle.{u} := pointedSimplicial_isCofibrant hCof _
  exact levelModelCategoryOfMonoidalGenerators.{u, u + 1, u} PointedSimplicialSet.circle
    pointedI pointedJ Cardinal.aleph0.{u}
    pointedI_domain_presentable pointedJ_domain_presentable

lemma simplicialLevelModelCategory_weakEquivalences :
    @weakEquivalences SymmetricSpectrum.{u} _
      (simplicialLevelModelCategory hCof hFib).categoryWithWeakEquivalences =
        levelProperty PointedSimplicialSet.circle (weakEquivalences PointedSimplicialSet.{u}) := rfl

lemma simplicialLevelModelCategory_fibrations :
    @fibrations SymmetricSpectrum.{u} _
      (simplicialLevelModelCategory hCof hFib).categoryWithFibrations =
        levelProperty PointedSimplicialSet.circle (fibrations PointedSimplicialSet.{u}) := rfl

lemma simplicialLevelModelCategory_generated :
    let := simplicialLevelModelCategory hCof hFib
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} simplicialLevelI.{u} simplicialLevelJ.{u} := by
  let : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} pointedI.{u} pointedJ.{u} :=
    pointedSimplicial_cofibrantlyGenerated hCof hFib
  let : MonoidalModelCategory PointedSimplicialSet.{u} :=
    pointedSimplicial_monoidalModel hCof hFib
  let : IsCofibrant (𝟙_ PointedSimplicialSet.{u}) := pointedSimplicial_isCofibrant hCof _
  let : IsCofibrant PointedSimplicialSet.circle.{u} := pointedSimplicial_isCofibrant hCof _
  exact levelModelCategoryOfMonoidalGenerators_generated.{u, u + 1, u} PointedSimplicialSet.circle
    pointedI pointedJ Cardinal.aleph0.{u}
    pointedI_domain_presentable pointedJ_domain_presentable

lemma simplicialLevel_evaluation_isRightQuillen (n : ℕ) :
    let := simplicialLevelModelCategory hCof hFib
    IsRightQuillen (SymmetricSpectrum.evaluation.{u} n) := by
  let := simplicialLevelModelCategory hCof hFib
  exact ⟨fun _ _ _ hf ↦ hf n, fun _ _ _ hf ↦ ⟨hf.1 n, hf.2 n⟩⟩

lemma simplicialLevel_freeAt_isLeftQuillen (n : ℕ) :
    let := simplicialLevelModelCategory hCof hFib
    IsLeftQuillen (SymmetricSpectrum.freeAt.{u} n) := by
  let := simplicialLevelModelCategory hCof hFib
  have := simplicialLevel_evaluation_isRightQuillen hCof hFib n
  exact isLeftQuillen_of_isRightQuillen (SymmetricSpectrum.freeAtAdjunction n)

lemma simplicialLevel_functorialFactorizations :
    let := simplicialLevelModelCategory hCof hFib
    (cofibrations SymmetricSpectrum.{u}).HasFunctorialFactorization
        (trivialFibrations SymmetricSpectrum.{u}) ∧
      (trivialCofibrations SymmetricSpectrum.{u}).HasFunctorialFactorization
        (fibrations SymmetricSpectrum.{u}) := by
  let := simplicialLevelModelCategory hCof hFib
  let := simplicialLevelModelCategory_generated hCof hFib
  exact ⟨_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_cofibration_trivialFibration
      simplicialLevelI simplicialLevelJ,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_trivialCofibration_fibration
      simplicialLevelI simplicialLevelJ⟩

end SerrePositivity.SimplicialModelInputs
