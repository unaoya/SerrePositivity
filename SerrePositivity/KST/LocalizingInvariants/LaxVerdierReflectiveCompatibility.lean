module

public import SerrePositivity.KST.LocalizingInvariants.LaxVerdierInvariantFiber
public import SerrePositivity.KST.LocalizingInvariants.TammeFiberSequence

/-!
概要：仮定付き lax Verdier 列の値の構成は、充満忠実右随伴の場合の既存結果と一致する。
方針：実際に構成済みの差の Verdier 列を代入し、同じ図式と積比較を回収する。
規約：商の存在を新たに仮定しない。使われ方：d8 と Tamme Prop. 11・Cor. 12 の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (v : E.obj ⟶ D.obj) (a : QCatAdjunction q.hom v) (hv : IsFullyFaithful v)

lemma laxQuotientVerdierSequence_reflective :
    laxQuotientVerdierSequence p q (pullbackInclusion p q) (exactLaxDifference p q)
      (laxDifference_isVerdier p q v a hv) = tammeVerdierSequence p q v a hv := rfl

namespace IsLocalizingInvariant
variable {Φ : StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)

lemma laxQuotientFiberTriangle_reflective :
    hΦ.laxQuotientFiberTriangle p q (pullbackInclusion p q) (exactLaxDifference p q)
      (laxDifference_isVerdier p q v a hv) = hΦ.tammeFiberTriangle p q v a hv := rfl

lemma laxQuotientFiberMiddleIso_reflective :
    hΦ.laxQuotientFiberMiddleIso p q (pullbackInclusion p q) (exactLaxDifference p q)
      (laxDifference_isVerdier p q v a hv) = hΦ.tammeFiberSquareMiddleIso p q v a hv := rfl

lemma laxQuotientDifferenceHom_reflective :
    hΦ.laxQuotientDifferenceHom p q (exactLaxDifference p q) =
      hΦ.tammeDifferenceHom p q := rfl

end IsLocalizingInvariant
end SerrePositivity.KST.LocalizingInvariants
