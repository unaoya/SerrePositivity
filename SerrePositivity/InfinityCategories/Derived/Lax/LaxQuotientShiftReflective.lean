module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.Exact.SuspensionExactFunctor
public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceCComparison
public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceDComparison
public import SerrePositivity.KST.LocalizingInvariants.LaxInclusions
public import SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientShiftLegs

/-!
概要：商が元の実 cofiber 差の場合、逆 shift で定めた二脚は元の p と q に戻る。
方針：C 側の全関手同型から ΣΩ を消し、D 側の既存比較を使う。
規約：q の充満忠実右随伴の場合にも同じ比較を使う。使われ方：既存 Tamme 列との整合。
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
namespace SerrePositivity.InfinityCategories.Derived.Lax
open SerrePositivity.KST.LocalizingInvariants
variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)

def laxQuotientCLeg_cofiberIso :
    FunctorIso (laxQuotientCLeg p q (exactLaxDifference p q)).hom p.hom := by
  have h := FunctorIso.postcomp (fromC_differenceIso p q)
    (SuspensionExact.equivalence E.obj).inv
  have e : FunctorIso ((p.hom ≫ SuspensionExact.map E.obj) ≫
      (SuspensionExact.equivalence E.obj).inv) p.hom := by
    have he := FunctorIso.precomp (SuspensionExact.equivalence E.obj).homInvIso p.hom
    change FunctorIso (p.hom ≫ (SuspensionExact.map E.obj ≫
      (SuspensionExact.equivalence E.obj).inv)) (p.hom ≫ 𝟙 E.obj) at he
    simpa only [Category.assoc, Category.comp_id] using he
  change FunctorIso (LaxInclusion.fromC p q ≫ laxDifference p q ≫
    (SuspensionExact.equivalence E.obj).inv) p.hom
  have hc := h ≪≫ e
  simpa only [Category.assoc, Category.comp_id] using hc

def laxQuotientDLeg_cofiberIso :
    FunctorIso (laxQuotientDLeg p q (exactLaxDifference p q)).hom q.hom :=
  fromD_differenceIso p q

variable (Φ : StableInfinity.{u} ⟶ Sp.{u})

lemma valueMap_laxQuotientCLeg_cofiber :
    SpectrumHo.hom (valueMap Φ (laxQuotientCLeg p q (exactLaxDifference p q))) =
      SpectrumHo.hom (valueMap Φ p) :=
  valueMap_hom_eq_of_functorIso Φ (laxQuotientCLeg_cofiberIso p q)

lemma valueMap_laxQuotientDLeg_cofiber :
    SpectrumHo.hom (valueMap Φ (laxQuotientDLeg p q (exactLaxDifference p q))) =
      SpectrumHo.hom (valueMap Φ q) :=
  valueMap_hom_eq_of_functorIso Φ (laxQuotientDLeg_cofiberIso p q)

end SerrePositivity.InfinityCategories.Derived.Lax

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg_cofiberIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.laxQuotientCLeg_cofiberIso := _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg_cofiberIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientDLeg_cofiberIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.laxQuotientDLeg_cofiberIso := _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientDLeg_cofiberIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.valueMap_laxQuotientCLeg_cofiber := _root_.SerrePositivity.InfinityCategories.Derived.Lax.valueMap_laxQuotientCLeg_cofiber

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.valueMap_laxQuotientDLeg_cofiber := _root_.SerrePositivity.InfinityCategories.Derived.Lax.valueMap_laxQuotientDLeg_cofiber

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.laxQuotientCLeg_cofiberIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg_cofiberIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.laxQuotientCLeg_cofiberIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg_cofiberIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.laxQuotientCLeg_cofiberIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg_cofiberIso._proof_3
