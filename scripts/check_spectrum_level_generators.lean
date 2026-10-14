import SerrePositivity.Spectra.ModelCategory.LevelFromGenerators
import SerrePositivity.Spectra.StageTwo
import Lean.Util.CollectAxioms

universe w u v
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra SerrePositivity
open SerrePositivity.GeneralSymmetricSpectrum SerrePositivity.SpectrumLevelModel
open SerrePositivity.ModelGeneration

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [HasColimitsOfSize.{w, w} C] [ModelCategory C] (K : C)
  [LocallySmall.{w} (GeneralSymmetricSpectrum C K)]
  (I J : MorphismProperty C) [CofibrantlyGenerated.{w} I J]
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (hI : ∀ {A B : C} (i : A ⟶ B), I i → IsCardinalPresentable A κ)
  (hJ : ∀ {A B : C} (i : A ⟶ B), J i → IsCardinalPresentable A κ)
  (heval : ∀ n m : ℕ, J.strictMap (freeAt (K := K) n ⋙ evaluation m) ≤
    trivialCofibrations C)

-- The image SOA and cell acyclicity are proved from these generator tests.
example : ModelCategory (GeneralSymmetricSpectrum C K) :=
  levelModelCategoryOfGenerators K I J κ hI hJ heval

example : let := levelModelCategoryOfGenerators K I J κ hI hJ heval
    weakEquivalences (GeneralSymmetricSpectrum C K) = levelProperty K (weakEquivalences C) :=
  levelModelCategoryOfGenerators_weakEquivalences K I J κ hI hJ heval

example : let := levelModelCategoryOfGenerators K I J κ hI hJ heval
    CofibrantlyGenerated.{w} (levelGenerators K I) (levelGenerators K J) :=
  levelModelCategoryOfGenerators_generated K I J κ hI hJ heval

example : let := levelModelCategoryOfGenerators K I J κ hI hJ heval
    (cofibrations (GeneralSymmetricSpectrum C K)).HasFunctorialFactorization
      (trivialFibrations (GeneralSymmetricSpectrum C K)) := by
  let := levelModelCategoryOfGenerators K I J κ hI hJ heval
  have := levelModelCategoryOfGenerators_generated K I J κ hI hJ heval
  exact hasFunctorialFactorization_cofibration_trivialFibration
    (levelGenerators K I) (levelGenerators K J)

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless (`SerrePositivity.Spectra.ModelCategory).isPrefixOf
        env.header.modules[idx.toNat]!.module do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "No level model declarations audited"
  logInfo m!"Spectrum level generator audit passed: {count} declarations, standard axioms only."
