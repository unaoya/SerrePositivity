import SerrePositivity.Spectra.Stable.Replacement
import SerrePositivity.Spectra.ModelCategory.LeftProper
import Lean.Util.CollectAxioms

universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity SerrePositivity.GeneralSymmetricSpectrum
open SerrePositivity.ModelGeneration SerrePositivity.SpectrumLevelModel
open SerrePositivity.SpectrumStabilization

-- Construct the original level model, both factorizations, the K-local model
-- and an actual accessible Omega replacement, all from source data.
example {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
    [ModelCategory C] [IsLocallyPresentable.{w} C]
    [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]
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
        (p : StableModelPresentation.{w} K cofSp fibSp (levelGenerators K I)),
        MorphismProperty.IsStableUnderCobaseChangeAgainst
          p.localization.model.categoryWithWeakEquivalences.weakEquivalences
          p.localization.model.categoryWithCofibrations.cofibrations ∧
        ∃ d : Bousfield.LocalReplacementData.{v, max u v}
            (C := GeneralSymmetricSpectrum C K) cofSp fibSp (localizingMaps K p.tests),
          d.L.IsAccessible.{w} ∧ (∀ E, IsFibrantOmegaSpectrum (d.L.obj E)) ∧
          p.localization.model.categoryWithWeakEquivalences.weakEquivalences =
            (weakEquivalences (GeneralSymmetricSpectrum C K)).inverseImage d.L := by
  obtain ⟨m, hW, hF, hC, hgen, hproper⟩ := exists_leftProper_levelModel_of_monoidal K I J
  let := m
  have : CofibrantlyGenerated.{w} (levelGenerators K I) (levelGenerators K J) := hgen
  have : (weakEquivalences (GeneralSymmetricSpectrum C K)).IsStableUnderCobaseChangeAgainst
      (cofibrations (GeneralSymmetricSpectrum C K)) := hproper
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
  obtain ⟨p⟩ := exists_stableModelPresentation K cofSp fibSp (levelGenerators K I)
    I J (levelGenerators K J) hW hF IS JS hcofW hfibW hcofV hfibV hcofM hfibM hw
  refine ⟨m, cofSp, fibSp, p, ?_, ?_⟩
  · exact p.leftProper K cofSp fibSp (levelGenerators K I) (levelGenerators K J)
      IS JS hcofW hfibW hcofV hfibV hcofM hfibM hw
  · exact p.exists_accessible_omegaReplacement K cofSp fibSp (levelGenerators K I)
      (levelGenerators K J) IS JS hcofW hfibW hcofV hfibV hcofM hfibM hw

-- The constructed localized model has actual accessible model factorizations.
example {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
    [ModelCategory C] [IsLocallyPresentable.{w} C] (K : C)
    [ModelCategory (GeneralSymmetricSpectrum C K)] [ModelCategory SSet.{v}]
    (cofSp : MorphismProperty.FunctorialFactorizationData
      (cofibrations (GeneralSymmetricSpectrum C K))
      (trivialFibrations (GeneralSymmetricSpectrum C K)))
    (fibSp : MorphismProperty.FunctorialFactorizationData
      (trivialCofibrations (GeneralSymmetricSpectrum C K))
      (fibrations (GeneralSymmetricSpectrum C K)))
    (IP : MorphismProperty (GeneralSymmetricSpectrum C K))
    (p : StableModelPresentation.{w} K cofSp fibSp IP) :
    let := p.localization.model
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      Nonempty (Smith.AccessibleModelFactorizations (GeneralSymmetricSpectrum C K) κ) :=
  p.exists_accessible_factorizations K cofSp fibSp IP

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.Spectra.ModelCategory.LeftProper,
    `SerrePositivity.Spectra.Stable.ModelCategory,
    `SerrePositivity.Spectra.Stable.Replacement]
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
  unless modules.size == expected.size do throwError "Some stable model modules were not audited"
  logInfo m!"Stable model audit passed: {count} declarations in {modules.size} modules, standard axioms only."
