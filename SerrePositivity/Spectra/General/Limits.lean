module
public import SerrePositivity.Spectra.General.Evaluation
public import SerrePositivity.Spectra.SymmetricSequence.DayAdjunction
public import SerrePositivity.Spectra.SymmetricSequence.Limits
public import SerrePositivity.CategoryTheory.Monoidal.Mod.Limits

/-! # Limits and colimits of general symmetric spectra

The module forgetful functor creates the supplied shapes. Evaluation preserves
those shapes. Larger universes require the corresponding limits/colimits in C.
-/
@[expose] public section
universe v u w w'
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.GeneralSymmetricSpectrum
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] (K : C)
  {J : Type w} [Category.{w'} J]

instance forget_createsLimits : CreatesLimitsOfSize.{w', w} (forget K) :=
  inferInstanceAs (CreatesLimitsOfSize.{w', w}
    (Mod.forget (D := SymmetricSequence C) (SymmetricSequence.tensorPowerSequence K)))

instance forget_createsColimitsOfShape [HasLimitsOfSize.{0, 0} C] :
    CreatesColimitsOfShape J (forget K) :=
  inferInstanceAs (CreatesColimitsOfShape J
    (Mod.forget (D := SymmetricSequence C) (SymmetricSequence.tensorPowerSequence K)))

instance forget_createsColimits [HasLimitsOfSize.{0, 0} C] :
    CreatesColimitsOfSize.{w', w} (forget K) where

instance [HasLimitsOfShape J C] : HasLimitsOfShape J (GeneralSymmetricSpectrum C K) :=
  inferInstanceAs (HasLimitsOfShape J
    (Mod (SymmetricSequence C) (SymmetricSequence.tensorPowerSequence K)))

instance [HasLimitsOfSize.{0, 0} C] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (GeneralSymmetricSpectrum C K) :=
  inferInstanceAs (HasColimitsOfShape J
    (Mod (SymmetricSequence C) (SymmetricSequence.tensorPowerSequence K)))

instance [HasLimitsOfSize.{w', w} C] :
    HasLimitsOfSize.{w', w} (GeneralSymmetricSpectrum C K) where

instance [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{w', w} C] :
    HasColimitsOfSize.{w', w} (GeneralSymmetricSpectrum C K) where

instance evaluation_preservesLimitsOfShape [HasLimitsOfShape J C] (n : ℕ) :
    PreservesLimitsOfShape J (evaluation (K := K) n) := by
  unfold evaluation
  infer_instance

instance evaluation_preservesColimitsOfShape [HasLimitsOfSize.{0, 0} C]
    [HasColimitsOfShape J C] (n : ℕ) :
    PreservesColimitsOfShape J (evaluation (K := K) n) := by
  unfold evaluation
  infer_instance

instance free_preservesColimits : PreservesColimitsOfSize.{w', w} (freeFunctor K) :=
  (freeForgetAdjunction K).leftAdjoint_preservesColimits

instance freeAt_preservesColimits (n : ℕ) :
    PreservesColimitsOfSize.{w', w} (freeAt (K := K) n) :=
  (freeAtAdjunction (K := K) n).leftAdjoint_preservesColimits

instance forget_preservesLimits [HasLimitsOfSize.{w', w} C] :
    PreservesLimitsOfSize.{w', w} (forget K) where

instance forget_preservesColimits [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{w', w} C] :
    PreservesColimitsOfSize.{w', w} (forget K) where

instance evaluation_preservesLimits [HasLimitsOfSize.{w', w} C] (n : ℕ) :
    PreservesLimitsOfSize.{w', w} (evaluation (K := K) n) where

instance evaluation_preservesColimits [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{w', w} C]
    (n : ℕ) : PreservesColimitsOfSize.{w', w} (evaluation (K := K) n) where

variable {K}
def limitLevelIso [HasLimitsOfShape J C] (F : J ⥤ GeneralSymmetricSpectrum C K) (n : ℕ) :
    level (limit F) n ≅ limit (F ⋙ evaluation n) := preservesLimitIso (evaluation n) F

@[reassoc (attr := simp)] lemma limitLevelIso_hom_π [HasLimitsOfShape J C]
    (F : J ⥤ GeneralSymmetricSpectrum C K) (n : ℕ) (j : J) :
    (limitLevelIso F n).hom ≫ limit.π (F ⋙ evaluation n) j = levelMap (limit.π F j) n :=
  preservesLimitIso_hom_π (evaluation n) F j

def colimitLevelIso [HasLimitsOfSize.{0, 0} C] [HasColimitsOfShape J C]
    (F : J ⥤ GeneralSymmetricSpectrum C K) (n : ℕ) :
    level (colimit F) n ≅ colimit (F ⋙ evaluation n) := preservesColimitIso (evaluation n) F

@[reassoc (attr := simp)] lemma colimitLevelIso_ι_hom [HasLimitsOfSize.{0, 0} C]
    [HasColimitsOfShape J C]
    (F : J ⥤ GeneralSymmetricSpectrum C K) (n : ℕ) (j : J) :
    levelMap (colimit.ι F j) n ≫ (colimitLevelIso F n).hom = colimit.ι (F ⋙ evaluation n) j :=
  ι_preservesColimitIso_hom (evaluation n) F j
end SerrePositivity.GeneralSymmetricSpectrum
