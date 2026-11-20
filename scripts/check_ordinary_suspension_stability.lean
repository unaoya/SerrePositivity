import SerrePositivity.HomotopicalAlgebra.Foundations
import SerrePositivity.Spectra.Stable.SimplicialStability
import SerrePositivity.Spectra.ModelCategory.PointedPresentability
import SerrePositivity.Spectra.Stable.DerivedTensorInverse
import SerrePositivity.Spectra.Stable.EnrichedModel
import Lean.Util.CollectAxioms

universe w v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity SerrePositivity.ModelGeneration SerrePositivity.Quillen
open SerrePositivity.GeneralSymmetricSpectrum SerrePositivity.SpectrumStabilization
open SerrePositivity.SpectrumLevelModel SerrePositivity.SimplicialModelInputs
open scoped ZeroObject



example [ModelCategory SSet.{u}]
    [original : ModelCategory (GeneralSymmetricSpectrum PointedSimplicialSet.{u} (PointedSimplicialSet.circle.{u}))]
    [∀ n : ℕ, IsLeftQuillen (freeAt (K := (PointedSimplicialSet.circle.{u})) n)]
    [CofibrantlyGenerated.{u} (levelGenerators (PointedSimplicialSet.circle.{u}) pointedI.{u}) (levelGenerators (PointedSimplicialSet.circle.{u}) pointedJ.{u})]
    [MorphismProperty.IsStableUnderCobaseChangeAgainst
      (weakEquivalences (GeneralSymmetricSpectrum PointedSimplicialSet.{u} (PointedSimplicialSet.circle.{u})))
      (cofibrations (GeneralSymmetricSpectrum PointedSimplicialSet.{u} (PointedSimplicialSet.circle.{u})))]
    (cofSp : MorphismProperty.FunctorialFactorizationData
      (cofibrations (GeneralSymmetricSpectrum PointedSimplicialSet.{u} (PointedSimplicialSet.circle.{u})))
      (trivialFibrations (GeneralSymmetricSpectrum PointedSimplicialSet.{u} (PointedSimplicialSet.circle.{u}))))
    (fibSp : MorphismProperty.FunctorialFactorizationData
      (trivialCofibrations (GeneralSymmetricSpectrum PointedSimplicialSet.{u} (PointedSimplicialSet.circle.{u})))
      (fibrations (GeneralSymmetricSpectrum PointedSimplicialSet.{u} (PointedSimplicialSet.circle.{u}))))
    (p : StableModelPresentation.{u} (PointedSimplicialSet.circle.{u}) cofSp fibSp (levelGenerators (PointedSimplicialSet.circle.{u}) pointedI.{u}))
    (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _)
    (hfib : fibrations SSet.{u} = SSet.modelCategoryQuillen.J.{u}.rlp)
    (hw : weakEquivalences SSet.{u} = SimplicialHomotopy.weakEquivalences)
    :
    let := pointedSimplicial_isLocallyPresentable.{u}
    let G := p.localization.generators
    let hg := p.localization.generated
    let lp := symmetricSpectrum_isLocallyPresentable (K := (PointedSimplicialSet.circle.{u}))
    let := p.localization.model
    let := hg
    let := lp
    let W := weakEquivalences (GeneralSymmetricSpectrum PointedSimplicialSet.{u} (PointedSimplicialSet.circle.{u}))
    ∃ (LSigma ROmega : W.Localization ⥤ W.Localization)
      (γ : W.Q ⋙ LSigma ⟶ SymmetricSpectrum.suspensionFunctor.{u} ⋙ W.Q)
      (ρ : SymmetricSpectrum.loopFunctor.{u} ⋙ W.Q ⟶ W.Q ⋙ ROmega),
      LSigma.IsLeftDerivedFunctor γ W ∧ ROmega.IsRightDerivedFunctor ρ W ∧
      ∃ e : W.Localization ≌ W.Localization,
        e.functor = HomotopySuspension.localizedFunctor (levelGenerators (PointedSimplicialSet.circle.{u}) pointedI) G W.Q ∧
          e.inverse = ROmega := by
  exact StableModelPresentation.exists_ordinarySuspensionLoopEquivalence
    (original := original) (cofSp := cofSp) (fibSp := fibSp) (p := p) hcof hfib hw

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Pointed.CylinderConeMap,
    `SerrePositivity.HomotopicalAlgebra.Pointed.SuspensionNaturality,
    `SerrePositivity.HomotopicalAlgebra.Quillen.CofibrantComparison,
    `SerrePositivity.Spectra.General.CircleSuspensionNaturality,
    `SerrePositivity.Spectra.General.DerivedSuspensionComparison,
    `SerrePositivity.Spectra.Stable.OrdinarySuspension,
    `SerrePositivity.Spectra.ModelCategory.PointedPresentability,
    `SerrePositivity.Spectra.Stable.SimplicialStability]
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
  unless modules.size == expected.size do throwError "Some ordinary suspension stability modules were not audited"
  logInfo m!"Ordinary suspension stability audit passed: {count} declarations in {modules.size} modules, standard axioms only."
