import SerrePositivity.Spectra.Stable.TensorInverseMap
import Lean.Util.CollectAxioms

universe w v u vH uH
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity SerrePositivity.GeneralSymmetricSpectrum SerrePositivity.SpectrumStabilization

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [ModelCategory C] [Quillen.IsQuillenBifunctor (curriedTensor C)] (K : C) [IsCofibrant K]
  [ModelCategory (GeneralSymmetricSpectrum C K)]
  [∀ n : ℕ, Quillen.IsLeftQuillen (freeAt (K := K) n)] [ModelCategory SSet.{v}]
  (cofC : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (cofSp : MorphismProperty.FunctorialFactorizationData
    (cofibrations (GeneralSymmetricSpectrum C K))
    (trivialFibrations (GeneralSymmetricSpectrum C K)))
  (fibSp : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations (GeneralSymmetricSpectrum C K))
    (fibrations (GeneralSymmetricSpectrum C K)))
  (IP : MorphismProperty (GeneralSymmetricSpectrum C K))
  (p : StableModelPresentation.{w} K cofSp fibSp IP)
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

-- A is arbitrary: membership in p.tests and a cofibrant unit are not inputs.
example (n : ℕ) (A : C) [IsCofibrant A] :
    p.localization.model.categoryWithWeakEquivalences.weakEquivalences (localizingMap K n A) :=
  p.localizingMap_isWeakEquivalence K cofC cofSp fibSp IP hcof hfib n A

-- An ordinary localization in an independent universe inverts the actual
-- tensor evaluation. No derived invertibility is assumed as an input.
example [IsCofibrant (𝟙_ C)] {H : Type uH} [Category.{vH} H]
    (Q : GeneralSymmetricSpectrum C K ⥤ H)
    [Q.IsLocalization p.localization.model.categoryWithWeakEquivalences.weakEquivalences] :
    IsIso (Q.map (tensorInverseEvaluation K)) := by
  exact Localization.inverts Q
    p.localization.model.categoryWithWeakEquivalences.weakEquivalences _
    (p.tensorInverseEvaluation_isWeakEquivalence K cofC cofSp fibSp IP hcof hfib)

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.Spectra.Stable.UniversalLocalizingMaps,
    `SerrePositivity.Spectra.Stable.TensorInverseMap]
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
  unless modules.size == expected.size do throwError "Some tensor inverse modules were not audited"
  logInfo m!"Tensor inverse map audit passed: {count} declarations in {modules.size} modules, standard axioms only."
