import SerrePositivity.HomotopicalAlgebra.Foundations
import SerrePositivity.Spectra.General.Foundations
import SerrePositivity.Spectra.StageTwo
import Lean.Util.CollectAxioms

universe w t u v u' v'
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.Quillen SerrePositivity.ModelGeneration
open SerrePositivity.ManyObjectModelTransfer

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {ι : Type t} [Small.{w} ι]
  [MonoidalCategory C] [BraidedCategory C] [ModelCategory C] [HasMonoidAxiom.{w} C]
  [HasFiniteLimits D] [HasFiniteColimits D] [HasColimitsOfSize.{w, w} D] [LocallySmall.{w} D]
  (L : ι → C ⥤ D) (R : ι → D ⥤ C) (adj : ∀ i, L i ⊣ R i)
  [∀ i, PreservesColimitsOfSize.{w, w} (R i)]
  [∀ i, PreservesColimitsOfShape WalkingSpan (R i)]
  (I J : MorphismProperty C) [CofibrantlyGenerated.{w} I J]
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (hI : ∀ {A B : C} (f : A ⟶ B), I f → IsCardinalPresentable A κ)
  (hJ : ∀ {A B : C} (f : A ⟶ B), J f → IsCardinalPresentable A κ)
  (H : ι → ι → C) (e : ∀ i j, L i ⋙ R j ≅ tensorLeft (H i j))

-- No image small-object argument, cell acyclicity, or model structure on D is assumed.
example : ModelCategory D := modelCategoryOfPresentableGenerators L R adj I J κ hI hJ H e

example : @weakEquivalences D _
    (modelCategoryOfPresentableGenerators L R adj I J κ hI hJ H e).categoryWithWeakEquivalences =
      EvaluationFamily.detected R (weakEquivalences C) :=
  modelCategoryOfPresentableGenerators_weakEquivalences L R adj I J κ hI hJ H e

example : @fibrations D _
    (modelCategoryOfPresentableGenerators L R adj I J κ hI hJ H e).categoryWithFibrations =
      EvaluationFamily.detected R (fibrations C) :=
  modelCategoryOfPresentableGenerators_fibrations L R adj I J κ hI hJ H e

example : let := modelCategoryOfPresentableGenerators L R adj I J κ hI hJ H e
    CofibrantlyGenerated.{w} (EvaluationFamily.generators L I) (EvaluationFamily.generators L J) :=
  modelCategoryOfPresentableGenerators_generated L R adj I J κ hI hJ H e

example (i : ι) : let := modelCategoryOfPresentableGenerators L R adj I J κ hI hJ H e
    IsRightQuillen (R i) := by
  let := modelCategoryOfPresentableGenerators L R adj I J κ hI hJ H e
  exact ⟨fun _ _ _ hf ↦ hf i, fun _ _ _ hf ↦ ⟨hf.1 i, hf.2 i⟩⟩

example : let := modelCategoryOfPresentableGenerators L R adj I J κ hI hJ H e
    (cofibrations D).HasFunctorialFactorization (trivialFibrations D) ∧
      (trivialCofibrations D).HasFunctorialFactorization (fibrations D) := by
  let := modelCategoryOfPresentableGenerators L R adj I J κ hI hJ H e
  have := modelCategoryOfPresentableGenerators_generated L R adj I J κ hI hJ H e
  exact ⟨hasFunctorialFactorization_cofibration_trivialFibration
      (EvaluationFamily.generators L I) (EvaluationFamily.generators L J),
    hasFunctorialFactorization_trivialCofibration_fibration
      (EvaluationFamily.generators L I) (EvaluationFamily.generators L J)⟩

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless #[`SerrePositivity.HomotopicalAlgebra.Transfer.EvaluationSmallness,
        `SerrePositivity.HomotopicalAlgebra.Monoidal.ManyObjectPresentability].contains
        env.header.modules[idx.toNat]!.module do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "No presentability transfer declarations audited"
  logInfo m!"Many-object presentability audit passed: {count} declarations, standard axioms only."
