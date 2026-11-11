import SerrePositivity.HomotopicalAlgebra.Generated.Replacement
import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.SimplicialLevel
import Lean.Util.CollectAxioms

universe w u v
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity SerrePositivity.ModelGeneration SerrePositivity.ModelReplacement

section General
variable (C : Type u) [Category.{v} C] [ModelCategory C]
  (I J : MorphismProperty C) [CofibrantlyGenerated.{w} I J]

example : ∃ Q : C ⥤ C, ∃ q : Q ⟶ 𝟭 C,
    ∀ X, IsCofibrant (Q.obj X) ∧ trivialFibrations C (q.app X) := by
  let := hasFunctorialFactorization_cofibration_trivialFibration I J
  exact ⟨cofibrantReplacement C, cofibrantComparison C,
    fun X ↦ ⟨cofibrantReplacement_isCofibrant C X, cofibrantComparison_trivialFibration C X⟩⟩

example : ∃ R : C ⥤ C, ∃ r : 𝟭 C ⟶ R,
    ∀ X, IsFibrant (R.obj X) ∧ trivialCofibrations C (r.app X) := by
  let := hasFunctorialFactorization_trivialCofibration_fibration I J
  exact ⟨fibrantReplacement C, fibrantComparison C,
    fun X ↦ ⟨fibrantReplacement_isFibrant C X, fibrantComparison_trivialCofibration C X⟩⟩
end General

section Concrete
open SerrePositivity.Inputs.Homotopy SerrePositivity.SimplicialModelInputs
local instance : ModelCategory SymmetricSpectrum.{u} := circleSpectrumLevelModel

example : ∃ Q : SymmetricSpectrum.{u} ⥤ SymmetricSpectrum.{u}, ∃ q : Q ⟶ 𝟭 _,
    ∀ E, IsCofibrant (Q.obj E) ∧ trivialFibrations SymmetricSpectrum.{u} (q.app E) := by
  let := circleSpectrumLevelModel_generated.{u}
  let := hasFunctorialFactorization_cofibration_trivialFibration
    simplicialLevelI.{u} simplicialLevelJ.{u}
  exact ⟨cofibrantReplacement _, cofibrantComparison _,
    fun E ↦ ⟨cofibrantReplacement_isCofibrant _ E, cofibrantComparison_trivialFibration _ E⟩⟩

example : ∃ R : SymmetricSpectrum.{u} ⥤ SymmetricSpectrum.{u}, ∃ r : 𝟭 _ ⟶ R,
    ∀ E, IsFibrant (R.obj E) ∧ trivialCofibrations SymmetricSpectrum.{u} (r.app E) := by
  let := circleSpectrumLevelModel_generated.{u}
  let := hasFunctorialFactorization_trivialCofibration_fibration
    simplicialLevelI.{u} simplicialLevelJ.{u}
  exact ⟨fibrantReplacement _, fibrantComparison _,
    fun E ↦ ⟨fibrantReplacement_isFibrant _ E, fibrantComparison_trivialCofibration _ E⟩⟩
end Concrete

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.modules[idx.toNat]!.module ==
        `SerrePositivity.HomotopicalAlgebra.Generated.Replacement do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "No functorial replacement declarations audited"
  logInfo m!"Functorial replacement audit passed: {count} declarations, standard axioms only."
