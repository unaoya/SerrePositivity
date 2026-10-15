import SerrePositivity.Spectra.Stable.OmegaLocalObjects
import SerrePositivity.Spectra.ModelCategory.Combinatorial
import SerrePositivity.Spectra.ModelCategory.FreeLevelCofibrations
import Lean.Util.CollectAxioms

universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity SerrePositivity.GeneralSymmetricSpectrum
open SerrePositivity.ModelGeneration SerrePositivity.SpectrumLevelModel
open SerrePositivity.SpectrumStabilization

-- Full consumer: the actual level model and both specified factorizations
-- are constructed. The small detecting family and the locality criterion
-- are outputs. No simplicial/tractable model source is assumed.
example {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
    [ModelCategory C] [IsLocallyPresentable.{w} C]
    [Quillen.IsQuillenBifunctor (curriedTensor C)] [IsCofibrant (𝟙_ C)]
    (K : C) [IsCofibrant K] (I J : MorphismProperty C) [CofibrantlyGenerated.{w} I J]
    [ModelCategory SSet.{w}] [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
    (IS JS : MorphismProperty SSet.{w}) [CofibrantlyGenerated.{w} IS JS]
    (hcofW : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
    (hfibW : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
    (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
    (hcofM : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
    (hfibM : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)
    (hw : weakEquivalences SSet.{w} = SimplicialHomotopy.weakEquivalences) :
    ∃ m : ModelCategory (GeneralSymmetricSpectrum C K),
      let := m
      ∃ (cofSp : MorphismProperty.FunctorialFactorizationData
          (cofibrations (GeneralSymmetricSpectrum C K))
          (trivialFibrations (GeneralSymmetricSpectrum C K)))
        (fibSp : MorphismProperty.FunctorialFactorizationData
          (trivialCofibrations (GeneralSymmetricSpectrum C K))
          (fibrations (GeneralSymmetricSpectrum C K)))
        (ι : Type w) (G : ι → C),
        (∀ i, IsCofibrant (G i)) ∧ (localizingMaps K G).IsSmall.{w} ∧
        (∀ {X Y : GeneralSymmetricSpectrum C K} (f : X ⟶ Y),
          localizingMaps K G f → IsCofibrant X ∧ IsCofibrant Y) ∧
        ∀ E : GeneralSymmetricSpectrum C K,
          Bousfield.localFibrantObjects cofSp fibSp (localizingMaps K G) E ↔
            IsFibrantOmegaSpectrum E := by
  have hj : J ≤ trivialCofibrations C := by
    rw [trivialCofibrations_eq_generated I J]
    exact J.le_llp_rlp
  have ht : ∀ n m : ℕ, J.strictMap (freeAt (K := K) n ⋙ evaluation m) ≤
      trivialCofibrations C := by
    intro n m X Y f hf
    cases hf with
    | map hf =>
      have : Cofibration _ := ⟨(hj _ hf).1⟩
      have : WeakEquivalence _ := ⟨(hj _ hf).2⟩
      exact evaluatedFree_trivialCofibration K _ n m
  obtain ⟨m, hW, hF, hC, hgen⟩ := exists_combinatorial_levelModel K I J ht
  let := m
  have : CofibrantlyGenerated.{w} (levelGenerators K I) (levelGenerators K J) := hgen
  have := hasFunctorialFactorization_cofibration_trivialFibration
    (levelGenerators K I) (levelGenerators K J)
  have := hasFunctorialFactorization_trivialCofibration_fibration
    (levelGenerators K I) (levelGenerators K J)
  let cofSp := MorphismProperty.functorialFactorizationData
    (cofibrations (GeneralSymmetricSpectrum C K))
    (trivialFibrations (GeneralSymmetricSpectrum C K))
  let fibSp := MorphismProperty.functorialFactorizationData
    (trivialCofibrations (GeneralSymmetricSpectrum C K))
    (fibrations (GeneralSymmetricSpectrum C K))
  obtain ⟨ι, G, hc, hs, he, ho⟩ := exists_omega_localizingMaps K I J hW hF cofSp fibSp
    IS JS hcofW hfibW hcofV hfibV hcofM hfibM hw
  exact ⟨m, cofSp, fibSp, ι, G, hc, hs, he, ho⟩

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Localization.FrameTargetTests,
    `SerrePositivity.HomotopicalAlgebra.Localization.ResolutionHomGenerators,
    `SerrePositivity.Spectra.ModelCategory.LevelFacts,
    `SerrePositivity.Spectra.Stable.OmegaDetection,
    `SerrePositivity.Spectra.Stable.OmegaLocalObjects]
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
  unless modules.size == expected.size do throwError "Some Omega locality modules were not audited"
  logInfo m!"Omega locality audit passed: {count} declarations in {modules.size} modules, standard axioms only."
