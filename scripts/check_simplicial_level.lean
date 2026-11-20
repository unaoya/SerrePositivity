import SerrePositivity.Spectra.ModelCategory.SimplicialLevel
import SerrePositivity.Spectra.General.Foundations
import SerrePositivity.Spectra.StageTwo
import Lean.Util.CollectAxioms

universe u
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity SerrePositivity.Quillen SerrePositivity.ModelGeneration
open SerrePositivity.InfinityCategories.HA.ModelCategoryComparison (CofibrantlyGenerated)
open SerrePositivity.SimplicialModelInputs
variable [ModelCategory SSet.{u}]
  (hCof : cofibrations SSet.{u} = MorphismProperty.monomorphisms SSet.{u})
  (hFib : fibrations SSet.{u} = SSet.modelCategoryQuillen.J.{u}.rlp)

-- Only the source model and its class equalities are inputs. In particular,
-- no spectrum model, image SOA, acyclicity, or size hypothesis is assumed.
example : ModelCategory SymmetricSpectrum.{u} := simplicialLevelModelCategory hCof hFib
example : CofibrantlyGenerated.{u} pointedI.{u} pointedJ.{u} :=
  pointedSimplicial_cofibrantlyGenerated hCof hFib
example (X : PointedSimplicialSet.{u}) : IsCofibrant X := pointedSimplicial_isCofibrant hCof X

example : let := simplicialLevelModelCategory hCof hFib
    CofibrantlyGenerated.{u} simplicialLevelI.{u} simplicialLevelJ.{u} :=
  simplicialLevelModelCategory_generated hCof hFib
example (n : ℕ) : let := simplicialLevelModelCategory hCof hFib
    IsRightQuillen (SymmetricSpectrum.evaluation.{u} n) :=
  simplicialLevel_evaluation_isRightQuillen hCof hFib n
example (n : ℕ) : let := simplicialLevelModelCategory hCof hFib
    IsLeftQuillen (SymmetricSpectrum.freeAt.{u} n) :=
  simplicialLevel_freeAt_isLeftQuillen hCof hFib n
example : let := simplicialLevelModelCategory hCof hFib
    (cofibrations SymmetricSpectrum.{u}).HasFunctorialFactorization
        (trivialFibrations SymmetricSpectrum.{u}) ∧
      (trivialCofibrations SymmetricSpectrum.{u}).HasFunctorialFactorization
        (fibrations SymmetricSpectrum.{u}) :=
  simplicialLevel_functorialFactorizations hCof hFib

example {E F : SymmetricSpectrum.{u}} (f : E ⟶ F) :
    let := simplicialLevelModelCategory hCof hFib
    WeakEquivalence f ↔ ∀ n, WeakEquivalence (GeneralSymmetricSpectrum.levelMap f n) := by
  let := simplicialLevelModelCategory hCof hFib
  simp only [weakEquivalence_iff]
  rfl
example {E F : SymmetricSpectrum.{u}} (f : E ⟶ F) :
    let := simplicialLevelModelCategory hCof hFib
    Fibration f ↔ ∀ n, Fibration (GeneralSymmetricSpectrum.levelMap f n) := by
  let := simplicialLevelModelCategory hCof hFib
  simp only [fibration_iff]
  rfl

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless #[`SerrePositivity.Spectra.ModelCategory.SimplicialMonoidal,
        `SerrePositivity.Spectra.ModelCategory.SimplicialLevel].contains
        env.header.modules[idx.toNat]!.module do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "No simplicial level declarations audited"
  logInfo m!"Simplicial level audit passed: {count} declarations, standard axioms only."
