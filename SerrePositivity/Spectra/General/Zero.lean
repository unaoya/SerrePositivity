module

public import SerrePositivity.Spectra.General.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! # Zero objects in general symmetric spectra over a pointed base

The actual module forgetful functor preserves the initial object and
reflects terminal objects. Its initial image is zero in the category of
symmetric sequences, so the actual initial spectrum is also terminal.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.GeneralSymmetricSpectrum
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [HasZeroObject C] (K : C)

lemma initial_isZero : IsZero (⊥_ (GeneralSymmetricSpectrum C K)) := by
  let F := forget K
  have : HasZeroObject (SymmetricSequence C) :=
    inferInstanceAs (HasZeroObject (FiniteBijection ⥤ C))
  have hi := initialIsInitial.isInitialObj F (⊥_ (GeneralSymmetricSpectrum C K))
  have hz : IsZero (F.obj (⊥_ (GeneralSymmetricSpectrum C K))) :=
    (isZero_zero (SymmetricSequence C)).of_iso
      (hi.uniqueUpToIso (isZero_zero (SymmetricSequence C)).isInitial)
  have ht := hz.isTerminal.isTerminalOfObj F (⊥_ (GeneralSymmetricSpectrum C K))
  exact ⟨fun Y ↦ ⟨⟨⟨initial.to Y⟩, fun f ↦ initialIsInitial.hom_ext f _⟩⟩,
    fun Y ↦ ⟨⟨⟨ht.from Y⟩, fun f ↦ ht.hom_ext f _⟩⟩⟩

instance : HasZeroObject (GeneralSymmetricSpectrum C K) := (initial_isZero K).hasZeroObject

instance : HasZeroMorphisms (GeneralSymmetricSpectrum C K) :=
  (initial_isZero K).hasZeroMorphisms

end SerrePositivity.GeneralSymmetricSpectrum
