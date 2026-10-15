import SerrePositivity.Spectra.ModelCategory.LeftProper
import Lean.Util.CollectAxioms

universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity SerrePositivity.GeneralSymmetricSpectrum
open SerrePositivity.ModelGeneration SerrePositivity.SpectrumLevelModel

-- Final consumer: no SOA on spectra, no generator cardinal bound and no
-- assumed level model. The source is not required to be simplicial or tractable.
example {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
    [ModelCategory C] [IsLocallyPresentable.{w} C]
    [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]
    [Quillen.IsQuillenBifunctor (curriedTensor C)] [IsCofibrant (𝟙_ C)]
    (K : C) [IsCofibrant K] (I J : MorphismProperty C) [CofibrantlyGenerated.{w} I J] :
    ∃ m : ModelCategory (GeneralSymmetricSpectrum C K),
      m.categoryWithWeakEquivalences.weakEquivalences = levelProperty K (weakEquivalences C) ∧
      m.categoryWithFibrations.fibrations = levelProperty K (fibrations C) ∧
      m.categoryWithCofibrations.cofibrations = (levelGenerators K I).rlp.llp ∧
      (let := m; CofibrantlyGenerated.{w} (levelGenerators K I) (levelGenerators K J)) ∧
      m.categoryWithWeakEquivalences.weakEquivalences.IsStableUnderCobaseChangeAgainst
        m.categoryWithCofibrations.cofibrations := by
  apply exists_leftProper_combinatorial_levelModel K I J
  · intro n m X Y f hf
    cases hf with
    | map hf =>
      have hi : I ≤ cofibrations C := by
        rw [cofibrations_eq_generated I J]
        exact I.le_llp_rlp
      have : Cofibration _ := ⟨hi _ hf⟩
      exact evaluatedFree_cofibration K _ n m
  · intro n m X Y f hf
    cases hf with
    | map hf =>
      have hj : J ≤ trivialCofibrations C := by
        rw [trivialCofibrations_eq_generated I J]
        exact J.le_llp_rlp
      have : Cofibration _ := ⟨(hj _ hf).1⟩
      have : WeakEquivalence _ := ⟨(hj _ hf).2⟩
      exact evaluatedFree_trivialCofibration K _ n m

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Transfer.EvaluationLeftProper,
    `SerrePositivity.Spectra.ModelCategory.FreeLevelCofibrations,
    `SerrePositivity.Spectra.ModelCategory.Combinatorial,
    `SerrePositivity.Spectra.ModelCategory.LeftProper]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  unless modules.size == expected.size do throwError "Some level properness modules were not audited"
  logInfo m!"Level left properness audit passed: {count} declarations in {modules.size} modules, standard axioms only."
