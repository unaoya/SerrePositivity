module

public import SerrePositivity.Spectra.SymmetricSequence.UnshiftedInternalHom
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-! # 対称列の各段のテンソル積と通常の内部Homの随伴 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

/-- 各段の通常のテンソル積を取る対称列の関手。 -/
def pointwiseTensorFunctor (X : C) : SymmetricSequence C ⥤ SymmetricSequence C where
  obj F := toFunctorCategory.obj F ⋙ tensorLeft X
  map g := CategoryTheory.Functor.whiskerRight (toFunctorCategory.map g) (tensorLeft X)

/-- 各段の通常の内部Homを取る対称列の関手。 -/
def unshiftedInternalHomFunctor (X : C) : SymmetricSequence C ⥤ SymmetricSequence C where
  obj := unshiftedInternalHom X
  map g := CategoryTheory.Functor.whiskerRight (toFunctorCategory.map g) (ihom X)

/-- 各段のテンソル積と通常の内部Homの随伴。 -/
def pointwiseTensorHomAdjunction (X : C) :
    pointwiseTensorFunctor X ⊣ unshiftedInternalHomFunctor X :=
  (ihom.adjunction X).whiskerRight FiniteBijection

omit [MonoidalClosed C] in
/-- 各段のテンソル積は基礎圏のテンソル積。 -/
lemma pointwiseTensorFunctor_level (X : C) (F : SymmetricSequence C) (q : ℕ) :
    level ((pointwiseTensorFunctor X).obj F) q = X ⊗ level F q := rfl

/-- 点ごとの随伴の評価は通常の内部Homの評価。 -/
lemma pointwiseTensorHomAdjunction_counit_app (X : C) (F : SymmetricSequence C)
    (a : FiniteBijection) :
    ((pointwiseTensorHomAdjunction X).counit.app F).app a = (ihom.ev X).app (F.obj a) := by
  exact Adjunction.whiskerRight_counit_app_app FiniteBijection (ihom.adjunction X) F a

end SerrePositivity.SymmetricSequence
