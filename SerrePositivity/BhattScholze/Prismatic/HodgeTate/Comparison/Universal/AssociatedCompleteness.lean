module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteCompletionIdempotent
public import Mathlib.RingTheory.Localization.Away.Basic
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic

/-!
# 選択生成元の単位倍によらない導来完備性

## 概要
同伴な二つの主元の導来完備性は、元の導来圏上で同値である。

## 方針
二つの標準局所化の基底線形同型を零次数へ置き、局所化からの全シフト射の消滅を移す。

## 規約
非有界な対象を扱う。通常の完備性や有限生成性へ置き換えない。

## 使われ方
Construction 6.1 の α(d)=p*u に対する完備化座標の照合。
-/

public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DerivedCompletion HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R]

/-- 同伴な主元の標準局所化は、元の基底環上で同型。 -/
def associatedLocalizationObjectIso (a b : R) (h : Associated a b) :
    localizationObject R a ≅ localizationObject R b := by
  letI : IsLocalization.Away a (Localization.Away b) :=
    IsLocalization.Away.of_associated h.symm
  let e := IsLocalization.algEquiv (Submonoid.powers a) (Localization.Away a) (Localization.Away b)
  exact (moduleObjectFunctor R).mapIso e.toLinearEquiv.toModuleIso

/-- 同伴な二つの主元は、全ての元の導来対象について同じ完備性を定める。 -/
theorem isComplete_associated_iff (a b : R) (h : Associated a b)
    (X : ConcreteDerivedCategory R) : IsComplete R a X ↔ IsComplete R b X := by
  let e := associatedLocalizationObjectIso a b h
  constructor
  · intro hX n f
    apply (cancel_epi e.hom).mp
    simpa only [comp_zero] using hX n (e.hom ≫ f)
  · intro hX n f
    apply (cancel_epi e.inv).mp
    simpa only [comp_zero] using hX n (e.inv ≫ f)

/-- 選択生成元の単位倍での導来完備性は、元の主元での完備性と同値。 -/
theorem isComplete_mul_unit_iff (a : R) (v : Rˣ) (X : ConcreteDerivedCategory R) :
    IsComplete R (a * (v : R)) X ↔ IsComplete R a X :=
  (isComplete_associated_iff a (a * (v : R)) ⟨v, rfl⟩ X).symm

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
