import SerrePositivity.Spectra.ModelCategory.SimplicialLevelTensor
import SerrePositivity.Spectra.General.Foundations
import SerrePositivity.Spectra.StageTwo
import Lean.Util.CollectAxioms

universe u
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModelInputs SerrePositivity.Quillen

-- The arrow comparison permits arbitrary source and target pushout choices.
example (m n : ℕ) {A B X Y : PointedSimplicialSet.{u}} (i : A ⟶ B) (j : X ⟶ Y)
    (sq : (curriedTensor PointedSimplicialSet.{u}).PushoutObjObj i j)
    (sp : (curriedTensor SymmetricSpectrum.{u}).PushoutObjObj
      ((SymmetricSpectrum.freeAt m).map i) ((SymmetricSpectrum.freeAt n).map j)) :
    Arrow.mk sp.ι ≅ Arrow.mk ((SymmetricSpectrum.freeAt (m + n)).map sq.ι) :=
  SymmetricSpectrum.freePushoutProductIso m n i j sq sp

variable [ModelCategory SSet.{u}]
  (hCof : cofibrations SSet.{u} = MorphismProperty.monomorphisms SSet.{u})
  (hFib : fibrations SSet.{u} = SSet.modelCategoryQuillen.J.{u}.rlp)

-- Spectrum monoidal compatibility, SM7 and unit cofibrancy are conclusions.
example : let := simplicialLevelModelCategory hCof hFib
    IsQuillenBifunctor (curriedTensor SymmetricSpectrum.{u}) :=
  simplicialLevelTensor_isQuillen hCof hFib
example : let := simplicialLevelModelCategory hCof hFib
    HasQuillenPullbackHom (MonoidalClosed.internalHom (C := SymmetricSpectrum.{u})) :=
  simplicialLevelTensor_SM7 hCof hFib
example : let := simplicialLevelModelCategory hCof hFib
    IsCofibrant (𝟙_ SymmetricSpectrum.{u}) := simplicialLevelTensor_unit_isCofibrant hCof hFib
example : let := simplicialLevelModelCategory hCof hFib
    MonoidalModelCategory SymmetricSpectrum.{u} := simplicialLevelTensor_monoidalModel hCof hFib

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless #[`SerrePositivity.Spectra.ModelCategory.FreePushoutProduct,
        `SerrePositivity.Spectra.ModelCategory.FreePushoutProductModel,
        `SerrePositivity.Spectra.ModelCategory.SimplicialLevelTensor].contains
        env.header.modules[idx.toNat]!.module do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "No spectrum level tensor declarations audited"
  logInfo m!"Spectrum level tensor audit passed: {count} declarations, standard axioms only."
