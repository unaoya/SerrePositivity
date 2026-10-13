module

public import SerrePositivity.Spectra.SymmetricSequence.Evaluation
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # 対称列の極限・余極限

関手圏の点ごとの構成を対称列の型へ移す。
Day convolutionのモノイダル構造には手を加えない。
-/

@[expose] public section

universe v u w w'

noncomputable section

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {J : Type w} [Category.{w'} J]

instance [HasLimitsOfShape J C] : HasLimitsOfShape J (SymmetricSequence C) :=
  inferInstanceAs (HasLimitsOfShape J (FiniteBijection ⥤ C))

instance [HasColimitsOfShape J C] : HasColimitsOfShape J (SymmetricSequence C) :=
  inferInstanceAs (HasColimitsOfShape J (FiniteBijection ⥤ C))

instance [HasLimitsOfSize.{w', w} C] : HasLimitsOfSize.{w', w} (SymmetricSequence C) where

instance [HasColimitsOfSize.{w', w} C] : HasColimitsOfSize.{w', w} (SymmetricSequence C) where

instance toFunctorCategory_preservesLimits :
    PreservesLimitsOfSize.{w', w} (toFunctorCategory (C := C)) :=
  inferInstanceAs (PreservesLimitsOfSize.{w', w} (𝟭 (FiniteBijection ⥤ C)))

instance toFunctorCategory_preservesColimits :
    PreservesColimitsOfSize.{w', w} (toFunctorCategory (C := C)) :=
  inferInstanceAs (PreservesColimitsOfSize.{w', w} (𝟭 (FiniteBijection ⥤ C)))

instance evaluation_preservesLimitsOfShape [HasLimitsOfShape J C] (n : ℕ) :
    PreservesLimitsOfShape J (evaluation (C := C) n) := by
  unfold evaluation
  infer_instance

instance evaluation_preservesColimitsOfShape [HasColimitsOfShape J C] (n : ℕ) :
    PreservesColimitsOfShape J (evaluation (C := C) n) := by
  unfold evaluation
  infer_instance

instance evaluation_preservesLimits [HasLimitsOfSize.{w', w} C] (n : ℕ) :
    PreservesLimitsOfSize.{w', w} (evaluation (C := C) n) where

instance evaluation_preservesColimits [HasColimitsOfSize.{w', w} C] (n : ℕ) :
    PreservesColimitsOfSize.{w', w} (evaluation (C := C) n) where

end SerrePositivity.SymmetricSequence
