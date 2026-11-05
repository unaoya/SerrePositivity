module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.Exact.SuspensionExactFunctor
public import SerrePositivity.KST.LocalizingInvariants.LaxInclusions
public import SerrePositivity.InfinityCategories.Derived.Lax.LaxVerdierProjectionFiber
public import SerrePositivity.InfinityCategories.Stable.Exact.SuspensionExactDiagrams
public import SerrePositivity.KST.LocalizingInvariants.SuspensionExactFunctor

/-!
概要：一般商 Q の二脚を、C 側の逆 shift を明示して元の完全関手から定める。
方針：C 包含の後の商を Q 内で逆 suspension し、ΣΩ の全関手同型を値へ移す。
規約：Q と商の普遍性は入力のまま。使われ方：d8 の符号付き cospan の二脚。
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
namespace SerrePositivity.InfinityCategories.Derived.Lax
open SerrePositivity.KST.LocalizingInvariants
variable {C D E Q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)
  (r : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (laxCategory p q) Q)

def laxQuotientCLeg : C ⟶ Q :=
  LaxInclusion.exactFromC p q ≫ r ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.SuspensionExact.inverseExactMap Q

def laxQuotientDLeg : D ⟶ Q := LaxInclusion.exactFromD p q ≫ r

def laxQuotientCLeg_suspensionIso : FunctorIso
    ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg p q r).hom ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.SuspensionExact.map Q.obj)
    (LaxInclusion.fromC p q ≫ r.hom) := by
  change FunctorIso
    ((LaxInclusion.fromC p q ≫ r.hom ≫ (_root_.SerrePositivity.InfinityCategories.Stable.Exact.SuspensionExact.equivalence Q.obj).inv) ≫
      (_root_.SerrePositivity.InfinityCategories.Stable.Exact.SuspensionExact.equivalence Q.obj).hom) (LaxInclusion.fromC p q ≫ r.hom)
  have e := FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Stable.Exact.SuspensionExact.equivalence Q.obj).invHomIso
    (LaxInclusion.fromC p q ≫ r.hom)
  simpa only [Category.assoc, Category.comp_id] using e

variable (Φ : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u} ⟶ Sp.{u})

lemma valueMap_quotientFromC_shift :
    SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromC p q)) ≫
        SpectrumHo.hom (valueMap Φ r) =
      SpectrumHo.hom (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg p q r)) ≫
        SpectrumHo.hom (valueMap Φ (SuspensionExact.exactMap Q)) := by
  change (stableValueFunctor Φ).map (LaxInclusion.exactFromC p q) ≫
    (stableValueFunctor Φ).map r = (stableValueFunctor Φ).map (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg p q r) ≫
      (stableValueFunctor Φ).map (SuspensionExact.exactMap Q)
  let f : C ⟶ Q := LaxInclusion.exactFromC p q ≫ r
  let g : C ⟶ Q := _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg p q r ≫ SuspensionExact.exactMap Q
  have e : FunctorIso f.hom g.hom := (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg_suspensionIso p q r).symm
  have h := valueMap_hom_eq_of_functorIso Φ e
  change (stableValueFunctor Φ).map f = (stableValueFunctor Φ).map g at h
  simpa only [f, g, CategoryTheory.Functor.map_comp] using h

lemma valueMap_quotientFromD :
    SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromD p q)) ≫
      SpectrumHo.hom (valueMap Φ r) = SpectrumHo.hom (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientDLeg p q r)) := by
  exact ((stableValueFunctor Φ).map_comp (LaxInclusion.exactFromD p q) r).symm

namespace IsLocalizingInvariant
open SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
variable {Φ} (hΦ : IsLocalizingInvariant Φ)

lemma laxQuotientProjectionDifferenceHom_shift_C :
    SpectrumHo.hom (Binary.inl (value Φ C) (value Φ D)) ≫
        (_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProjectionDifferenceHom hΦ) p q r =
      SpectrumHo.hom (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg p q r)) ≫
        SpectrumHo.hom (valueMap Φ (SuspensionExact.exactMap Q)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProjectionDifferenceHom_C]
  exact _root_.SerrePositivity.InfinityCategories.Derived.Lax.valueMap_quotientFromC_shift p q r Φ

lemma laxQuotientProjectionDifferenceHom_shift_D :
    SpectrumHo.hom (Binary.inr (value Φ C) (value Φ D)) ≫
      (_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProjectionDifferenceHom hΦ) p q r =
        SpectrumHo.hom (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientDLeg p q r)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProjectionDifferenceHom_D]
  exact _root_.SerrePositivity.InfinityCategories.Derived.Lax.valueMap_quotientFromD p q r Φ

end IsLocalizingInvariant
end SerrePositivity.InfinityCategories.Derived.Lax

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.laxQuotientCLeg := _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg_suspensionIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.laxQuotientCLeg_suspensionIso := _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg_suspensionIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientDLeg (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.laxQuotientDLeg := _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientDLeg

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.valueMap_quotientFromC_shift := _root_.SerrePositivity.InfinityCategories.Derived.Lax.valueMap_quotientFromC_shift

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.valueMap_quotientFromD := _root_.SerrePositivity.InfinityCategories.Derived.Lax.valueMap_quotientFromD

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProjectionDifferenceHom_shift_C := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProjectionDifferenceHom_shift_C

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProjectionDifferenceHom_shift_D := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProjectionDifferenceHom_shift_D

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.laxQuotientCLeg_suspensionIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg_suspensionIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.laxQuotientCLeg_suspensionIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg_suspensionIso._proof_2
