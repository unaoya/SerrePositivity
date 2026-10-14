import SerrePositivity.Spectra.ModelCategory.MonoidalLevel
import SerrePositivity.Spectra.StageTwo
import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w u v
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra SerrePositivity
open CategoryTheory.MonoidalCategory
open SerrePositivity.GeneralSymmetricSpectrum SerrePositivity.SpectrumLevelModel
open SerrePositivity.ModelGeneration SerrePositivity.Quillen

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [HasColimitsOfSize.{w, w} C] [ModelCategory C]
  [IsQuillenBifunctor (curriedTensor C)] [IsCofibrant (𝟙_ C)] (K : C) [IsCofibrant K]
  [LocallySmall.{w} (GeneralSymmetricSpectrum C K)]
  (I J : MorphismProperty C) [CofibrantlyGenerated.{w} I J]
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (hI : ∀ {A B : C} (i : A ⟶ B), I i → IsCardinalPresentable A κ)
  (hJ : ∀ {A B : C} (i : A ⟶ B), J i → IsCardinalPresentable A κ)

-- No SOA, cell acyclicity or free-generator tests on spectra are assumed.
example : ModelCategory (GeneralSymmetricSpectrum C K) :=
  levelModelCategoryOfMonoidalGenerators K I J κ hI hJ

example : let := levelModelCategoryOfMonoidalGenerators K I J κ hI hJ
    CofibrantlyGenerated.{w} (levelGenerators K I) (levelGenerators K J) :=
  levelModelCategoryOfMonoidalGenerators_generated K I J κ hI hJ

example (n : ℕ) : let := levelModelCategoryOfMonoidalGenerators K I J κ hI hJ
    IsRightQuillen (evaluation (K := K) n) := by
  let := levelModelCategoryOfMonoidalGenerators K I J κ hI hJ
  exact ⟨fun _ _ _ hf ↦ hf n, fun _ _ _ hf ↦ ⟨hf.1 n, hf.2 n⟩⟩

example : let := levelModelCategoryOfMonoidalGenerators K I J κ hI hJ
    (cofibrations (GeneralSymmetricSpectrum C K)).HasFunctorialFactorization
      (trivialFibrations (GeneralSymmetricSpectrum C K)) := by
  let := levelModelCategoryOfMonoidalGenerators K I J κ hI hJ
  have := levelModelCategoryOfMonoidalGenerators_generated K I J κ hI hJ
  exact hasFunctorialFactorization_cofibration_trivialFibration
    (levelGenerators K I) (levelGenerators K J)

example (n m : ℕ) : Quiver.IsThin
    (CostructuredArrow (FiniteBijection.addRight n) (FiniteBijection.of m)) := inferInstance

example (n m : ℕ) : IsGroupoid
    (CostructuredArrow (FiniteBijection.addRight n) (FiniteBijection.of m)) := inferInstance

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless #[`SerrePositivity.Spectra.ModelCategory,
        `SerrePositivity.CategoryTheory.Groupoid.ThinComponents,
        `SerrePositivity.CategoryTheory.FiniteBijectionInduction,
        `SerrePositivity.HomotopicalAlgebra.Monoidal.CofibrantTensor].any (·.isPrefixOf mod) do
      continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "No monoidal level declarations audited"
  logInfo m!"Monoidal spectrum level audit passed: {count} declarations, standard axioms only."
