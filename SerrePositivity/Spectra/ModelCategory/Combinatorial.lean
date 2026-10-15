module

public import SerrePositivity.Spectra.General.Limits
public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleLimits
public import SerrePositivity.HomotopicalAlgebra.Monoidal.ModulePresentability

/-! # Local presentability of general symmetric spectra

The underlying category is the actual Mathlib category of modules over Sym(K)
in Day convolution. Functor-category presentability and the proved free-module
criterion give local presentability for every suspension coordinate K.
No model structure or cofibrancy condition on K is needed for this fact.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SpectrumLevelModel
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [IsLocallyPresentable.{w} C]

omit [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasColimitsOfSize.{0, 0} C] in
lemma symmetricSequence_isLocallyPresentable :
    IsLocallyPresentable.{w} (SymmetricSequence C) := by
  have : IsLocallyPresentable.{w} (FiniteBijection ⥤ C) :=
    Smith.AccessibleLimits.functorCategory_isLocallyPresentable.{w}
      (C := C) FiniteBijection
  exact this

lemma symmetricSpectrum_isLocallyPresentable (K : C) :
    IsLocallyPresentable.{w} (GeneralSymmetricSpectrum C K) := by
  have := symmetricSequence_isLocallyPresentable (C := C)
  exact MonoidalModulePresentability.isLocallyPresentable
    (SymmetricSequence.tensorPowerSequence K)

end SerrePositivity.SpectrumLevelModel
