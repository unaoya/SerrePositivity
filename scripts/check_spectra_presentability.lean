import SerrePositivity.Spectra.ModelCategory.Combinatorial
import Lean.Util.CollectAxioms

universe w v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SerrePositivity

-- Independent category, Hom and presentability universes; no accessibility
-- or local presentability of D is presumed.
example {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
    [G.Faithful] [G.ReflectsIsomorphisms] [G.IsAccessible.{w}]
    [IsLocallyPresentable.{w} C] [HasColimitsOfSize.{w, w} D] [LocallySmall.{w} D] :
    IsLocallyPresentable.{w} D :=
  Smith.ConservativeAdjunction.isLocallyPresentable a

-- Actual internal modules over an arbitrary monoid, with no model structure.
example {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [IsLocallyPresentable.{w} C]
    [∀ X : C, PreservesColimitsOfSize.{w, w} (tensorLeft X)]
    (M : C) [MonObj M] : IsLocallyPresentable.{w} (Mod C M) :=
  MonoidalModulePresentability.isLocallyPresentable M

-- The actual Day-convolution module category, with arbitrary coordinate K.
example {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalClosed C] [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]
    [IsLocallyPresentable.{w} C] (K : C) :
    IsLocallyPresentable.{w} (GeneralSymmetricSpectrum C K) :=
  SpectrumLevelModel.symmetricSpectrum_isLocallyPresentable K

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Smith.ConservativeAdjunction,
    `SerrePositivity.HomotopicalAlgebra.Monoidal.ModulePresentability,
    `SerrePositivity.Spectra.ModelCategory.Combinatorial]
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
  unless modules.size == expected.size do throwError "Some presentability modules were not audited"
  logInfo m!"Spectrum presentability audit passed: {count} declarations in {modules.size} modules, standard axioms only."
