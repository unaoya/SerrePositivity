import SerrePositivity.Spectra.ModelCategory.LevelRecognition
import SerrePositivity.Spectra.StageTwo
import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w u v
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra SerrePositivity
open SerrePositivity.SpectrumLevelModel SerrePositivity.ModelGeneration

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [ModelCategory C] (K : C) (I J : MorphismProperty C) [CofibrantlyGenerated.{w} I J]
  [(levelGenerators K I).HasSmallObjectArgument.{w}]
  [(levelGenerators K J).HasSmallObjectArgument.{w}]
  (h : MorphismProperty.transfiniteCompositions.{w}
    (MorphismProperty.coproducts.{w} (levelGenerators K J)).pushouts ≤
      levelProperty K (weakEquivalences C))

example : ModelCategory (GeneralSymmetricSpectrum C K) := levelModelCategory K I J h

example : let := levelModelCategory K I J h
    weakEquivalences (GeneralSymmetricSpectrum C K) = levelProperty K (weakEquivalences C) :=
  levelModelCategory_weakEquivalences K I J h

example : let := levelModelCategory K I J h
    fibrations (GeneralSymmetricSpectrum C K) = levelProperty K (fibrations C) :=
  levelModelCategory_fibrations K I J h

example : let := levelModelCategory K I J h
    CofibrantlyGenerated.{w} (levelGenerators K I) (levelGenerators K J) :=
  levelModelCategory_generated K I J h

example (n : ℕ) : let := levelModelCategory K I J h
    SerrePositivity.Quillen.IsRightQuillen (GeneralSymmetricSpectrum.evaluation (K := K) n) :=
  evaluation_isRightQuillen K I J h n

example (n : ℕ) : let := levelModelCategory K I J h
    SerrePositivity.Quillen.IsLeftQuillen (GeneralSymmetricSpectrum.freeAt (K := K) n) :=
  freeAt_isLeftQuillen K I J h n

example : let := levelModelCategory K I J h
    (cofibrations (GeneralSymmetricSpectrum C K)).HasFunctorialFactorization
      (trivialFibrations (GeneralSymmetricSpectrum C K)) :=
  (levelFunctorialFactorizations K I J h).1

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
  logInfo m!"Spectrum level model audit passed: {count} declarations, standard axioms only."
