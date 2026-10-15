import SerrePositivity.Spectra.Stable.InternalHomOmega
import Lean.Util.CollectAxioms

universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity SerrePositivity.GeneralSymmetricSpectrum
open SerrePositivity.SpectrumStabilization

-- The exchange is an actual isomorphism in any closed braided category.
example {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] (X K Z : C) :
    (ihom X).obj ((ihom K).obj Z) ≅ (ihom K).obj ((ihom X).obj Z) :=
  InternalHomExchange.iso X K Z

-- No model structure on spectra, small generating family, simplicial source
-- or localization is assumed in these Omega-preservation results.
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [ModelCategory C] [Quillen.IsQuillenBifunctor (curriedTensor C)]
  (K : C) [IsCofibrant K] (X : C) [IsCofibrant X]
  (E : GeneralSymmetricSpectrum C K) (hE : IsFibrantOmegaSpectrum E)

example (n : ℕ) : IsFibrantOmegaSpectrum (shiftedHom n X E) :=
  shiftedHom_isFibrantOmega n X E hE

example (n : ℕ) : IsFibrantOmegaSpectrum (internalHom ((freeAt (K := K) n).obj X) E) :=
  internalHomFreeAt_isFibrantOmega n X E hE

example : IsFibrantOmegaSpectrum (cotensor X E) := cotensor_isFibrantOmega X E hE

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.CategoryTheory.Monoidal.InternalHomExchange,
    `SerrePositivity.Spectra.General.ShiftedHom,
    `SerrePositivity.Spectra.General.ShiftedHomSuspension,
    `SerrePositivity.Spectra.General.ShiftedHomAdjoint,
    `SerrePositivity.Spectra.Stable.InternalHomOmega]
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
  unless modules.size == expected.size do throwError "Some internal Hom Omega modules were not audited"
  logInfo m!"Internal Hom Omega audit passed: {count} declarations in {modules.size} modules, standard axioms only."
