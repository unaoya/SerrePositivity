module

public import SerrePositivity.EInfinity.Hammock.MarkedValueSpineDescent
public import Mathlib.CategoryTheory.Localization.Construction

/-!
# 元の通常の局所化と指定値の因子列の圏の比較

概要：元の局所化から値の因子列への関手と逆向きの延長を構成する。
方針：元の指定矢の反転と二つの厳密な延長の回収式を使う。
規約：元の Q と元の全自由射列への一致を保持する。
使われ方：値の因子列の Hom と元の通常の局所化 Hom の同定。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)

def localizationToValue : letI := valueCategory W
    W.paths.Localization ⥤ ValueObjects C := by
  letI := valueCategory W
  exact Localization.Construction.lift (valueLift W) (valueLift_inverts W)

def valueToLocalization : letI := valueCategory W
    ValueObjects C ⥤ W.paths.Localization := by
  letI := valueCategory W
  exact valueDescent W W.paths.Q W.paths.Q_inverts

lemma localizationToValue_fac : letI := valueCategory W
    W.paths.Q ⋙ localizationToValue W = valueLift W := by
  let := valueCategory W
  exact Localization.Construction.fac (valueLift W) (valueLift_inverts W)

lemma valueToLocalization_fac : letI := valueCategory W
    valueLift W ⋙ valueToLocalization W = W.paths.Q :=
  valueDescent_fac W _ _

lemma localizationToValue_valueToLocalization : letI := valueCategory W
    localizationToValue W ⋙ valueToLocalization W = 𝟭 W.paths.Localization := by
  let := valueCategory W
  apply Localization.Construction.uniq (W := W.paths)
  rw [← Functor.assoc, localizationToValue_fac, valueToLocalization_fac, Functor.comp_id]

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
