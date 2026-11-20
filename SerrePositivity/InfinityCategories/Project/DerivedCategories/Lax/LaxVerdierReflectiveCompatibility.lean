module


public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxVerdierInvariantFiber
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.TammeFiberSequence

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
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax
open _root_.SerrePositivity.KST.LocalizingInvariants
variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (v : E.obj ⟶ D.obj) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction q.hom v) (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful v)

lemma laxQuotientVerdierSequence_reflective :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientVerdierSequence p q (pullbackInclusion p q) (exactLaxDifference p q)
      (laxDifference_isVerdier p q v a hv) = tammeVerdierSequence p q v a hv := rfl

namespace IsLocalizingInvariant
open _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
variable {Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)

lemma laxQuotientFiberTriangle_reflective :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle p q (pullbackInclusion p q) (exactLaxDifference p q) (laxDifference_isVerdier p q v a hv) hΦ) = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeFiberTriangle hΦ) p q v a hv := rfl

lemma laxQuotientFiberMiddleIso_reflective :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.IsLocalizingInvariant.laxQuotientFiberMiddleIso p q (pullbackInclusion p q) (exactLaxDifference p q) (laxDifference_isVerdier p q v a hv) hΦ) = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeFiberSquareMiddleIso hΦ) p q v a hv := rfl

lemma laxQuotientDifferenceHom_reflective :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.IsLocalizingInvariant.laxQuotientDifferenceHom p q (exactLaxDifference p q) hΦ) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeDifferenceHom hΦ) p q := rfl

end IsLocalizingInvariant
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
