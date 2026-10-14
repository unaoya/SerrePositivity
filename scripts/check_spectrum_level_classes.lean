import SerrePositivity.Spectra.ModelCategory.LevelClasses
import Lean.Util.CollectAxioms

universe w u v
open CategoryTheory HomotopicalAlgebra SerrePositivity
open SerrePositivity.SpectrumLevelModel SerrePositivity.ModelGeneration

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [CategoryTheory.Limits.HasColimitsOfSize.{0, 0} C] (K : C)

example (P : MorphismProperty C) :
    (levelGenerators K P).rlp = levelProperty K P.rlp := levelGenerators_rlp K P

-- No model structure on GeneralSymmetricSpectrum C K is assumed here.
example [ModelCategory C] (I J : MorphismProperty C) [CofibrantlyGenerated.{w} I J] :
    (levelGenerators K I).rlp = levelProperty K (trivialFibrations C) :=
  generatingCofibrations_rlp K I J

example [ModelCategory C] (I J : MorphismProperty C) [CofibrantlyGenerated.{w} I J] :
    (levelGenerators K J).rlp = levelProperty K (fibrations C) :=
  generatingTrivialCofibrations_rlp K I J

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.modules[idx.toNat]!.module ==
        `SerrePositivity.Spectra.ModelCategory.LevelClasses do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "No level class declarations audited"
  logInfo m!"Spectrum level class audit passed: {count} declarations, standard axioms only."
