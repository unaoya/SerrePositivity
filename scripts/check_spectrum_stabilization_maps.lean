import SerrePositivity.Spectra.Stable.CofibrantLocalizingMaps
import SerrePositivity.Spectra.Stable.LocalizingHom
import SerrePositivity.Spectra.Stable.Omega
import SerrePositivity.Spectra.Stable.FrameLocality
import Lean.Util.CollectAxioms

universe w t v u
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed HomotopicalAlgebra
open SerrePositivity SerrePositivity.GeneralSymmetricSpectrum
open SerrePositivity.SpectrumStabilization SerrePositivity.HomotopyFunctionComplex

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [CategoryTheory.Limits.HasColimitsOfSize.{0, 0} C] (K : C)

-- Actual arrows, natural in the input. No model structure enters their definition.
example (n : ℕ) (A : C) :
    (freeAt (K := K) (n + 1)).obj (A ⊗ K) ⟶ (freeAt (K := K) n).obj A :=
  localizingMap K n A

example {ι : Type t} [Small.{w} ι] (A : ι → C) :
    (localizingMaps K A).IsSmall.{w} := inferInstance

-- All simplices in the Hom comparison, for any cosimplicial object.
example (n : ℕ) (A : SimplexCategory ⥤ C) (E : GeneralSymmetricSpectrum C K) :
    Arrow.mk ((cosimplicialHomMap (Functor.whiskerLeft A (stabilizationMap K n))).app E) ≅
      Arrow.mk ((cosimplicialHom A).map (adjointStructureMap E n)) :=
  localizingHomArrowIso K n A E

section Models
variable [ModelCategory C] [Quillen.IsQuillenBifunctor (curriedTensor C)] [IsCofibrant K]
  [ModelCategory (GeneralSymmetricSpectrum C K)]
  [∀ n : ℕ, Quillen.IsLeftQuillen (freeAt (K := K) n)]

example {ι : Type t} (A : ι → C)
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    {X Y : GeneralSymmetricSpectrum C K} (f : X ⟶ Y)
    (hf : localizingMaps K (fun i ↦ (cofibrantSource cof).obj (A i)) f) :
    IsCofibrant X ∧ IsCofibrant Y :=
  replacedLocalizingMaps_endpoints_cofibrant K A cof f hf

example {E F : GeneralSymmetricSpectrum C K} (f : E ⟶ F)
    (hE : ∀ n : ℕ, IsFibrant (level E n)) (hF : ∀ n : ℕ, IsFibrant (level F n))
    (hf : ∀ n : ℕ, weakEquivalences C (levelMap f n)) :
    IsOmegaSpectrum E ↔ IsOmegaSpectrum F :=
  isOmegaSpectrum_iff_of_levelWeakEquivalence f hE hF hf

-- The original ordinary RMap test is computed from an actual source frame,
-- not replaced by a definition of local objects in terms of bonding maps.
example [ModelCategory SSet.{v}]
    (cofC : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (cofSp : MorphismProperty.FunctorialFactorizationData
      (cofibrations (GeneralSymmetricSpectrum C K))
      (trivialFibrations (GeneralSymmetricSpectrum C K)))
    (fibSp : MorphismProperty.FunctorialFactorizationData
      (trivialCofibrations (GeneralSymmetricSpectrum C K))
      (fibrations (GeneralSymmetricSpectrum C K)))
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (n : ℕ) (X : C) [IsCofibrant X] (E : GeneralSymmetricSpectrum C K) :
    Bousfield.mappingTest cofSp fibSp E (localizingMap K n X) ↔
      weakEquivalences SSet.{v} ((cosimplicialHom
        ((Reedy.cosimplicialResolutionFamily cofC).obj.obj X)).map
          (adjointStructureMap ((fibrantTarget fibSp).obj E) n)) :=
  mappingTest_localizingMap_iff K cofC cofSp fibSp hcof n X E
end Models

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.Spectra.General.Suspension,
    `SerrePositivity.Spectra.Stable.LocalizingMaps,
    `SerrePositivity.Spectra.Stable.CofibrantLocalizingMaps,
    `SerrePositivity.Spectra.Stable.LocalizingHom,
    `SerrePositivity.Spectra.Stable.Omega,
    `SerrePositivity.HomotopicalAlgebra.Localization.FrameArrowTests,
    `SerrePositivity.Spectra.Stable.FrameLocality]
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
  unless modules.size == expected.size do throwError "Some stabilization map modules were not audited"
  logInfo m!"Stabilization maps audit passed: {count} declarations in {modules.size} modules, standard axioms only."
