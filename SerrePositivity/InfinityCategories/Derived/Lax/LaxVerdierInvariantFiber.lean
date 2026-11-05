module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.TammeSplitting
public import SerrePositivity.KST.LocalizingInvariants.InvariantLongExact

/-!
概要：元の lax pullback を中項とする仮定付き Verdier 列から不変量の実 fiber 列を得る。
方針：K-5 の任意 Verdier 列の fiber 性と、元の二因子への積分裂を組み合わせる。
規約：安定な商 Q と IsVerdierSequence は入力。使われ方：B 案の抽象 Land–Tamme d8。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
namespace SerrePositivity.InfinityCategories.Derived.Lax
open SerrePositivity.KST.LocalizingInvariants
variable {C D E A Q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i r)

def laxQuotientVerdierSequence : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.{u} where
  left := A
  middle := laxCategory p q
  right := Q
  inclusion := i
  projection := r
  isVerdier := h

namespace IsLocalizingInvariant
open SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
variable {Φ : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)

def laxQuotientFiberTriangle : ZeroTriangle Sp.{u} :=
  hΦ.abstractFiberTriangle (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientVerdierSequence p q i r h)

lemma laxQuotientFiberTriangle_isFiber : IsFiberSequence ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle p q i r h hΦ)) :=
  hΦ.abstractFiberTriangle_isFiber (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientVerdierSequence p q i r h)

lemma laxQuotientFiberTriangle_bottom :
    squareBottomEdge ≫ ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle p q i r h hΦ)).square =
      SSet.yonedaEquiv.symm (Φ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow i).edge) :=
  hΦ.abstractFiberTriangle_bottom (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientVerdierSequence p q i r h)

lemma laxQuotientFiberTriangle_right :
    squareRightEdge ≫ ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle p q i r h hΦ)).square =
      SSet.yonedaEquiv.symm (Φ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow r).edge) :=
  hΦ.abstractFiberTriangle_right (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientVerdierSequence p q i r h)

def laxQuotientFiberMiddleIso :
    squareHoVertex ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle p q i r h hΦ)).square 1 0 ≅
      SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) :=
  hΦ.fiberMiddleIso (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientVerdierSequence p q i r h) ≪≫ (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeSplitEquivalence hΦ) p q

def laxQuotientDifferenceHom : SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) ⟶
    SpectrumHo.obj (value Φ Q) :=
  ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeSplitComparison hΦ) p q).hom ≫ SpectrumHo.hom (valueMap Φ r)

lemma laxQuotientFiberMiddleIso_right :
    ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientFiberMiddleIso p q i r h hΦ)).hom ≫ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientDifferenceHom p q r hΦ) =
      squareHoRight ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle p q i r h hΦ)).square ≫
        (hΦ.fiberRightIso (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientVerdierSequence p q i r h)).hom := by
  change ((hΦ.fiberMiddleIso (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientVerdierSequence p q i r h)).hom ≫
    ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeSplitComparison hΦ) p q).inv) ≫ (((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeSplitComparison hΦ) p q).hom ≫ _) = _
  rw [Category.assoc, Iso.inv_hom_id_assoc]
  exact hΦ.fiber_right_naturality (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientVerdierSequence p q i r h)

lemma laxQuotientDifferenceHom_C : SpectrumHo.hom (Binary.inl (value Φ C) (value Φ D)) ≫
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientDifferenceHom p q r hΦ) =
      SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromC p q)) ≫
        SpectrumHo.hom (valueMap Φ r) := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientDifferenceHom, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeSplitComparison_C]

lemma laxQuotientDifferenceHom_D : SpectrumHo.hom (Binary.inr (value Φ C) (value Φ D)) ≫
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientDifferenceHom p q r hΦ) =
      SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromD p q)) ≫
        SpectrumHo.hom (valueMap Φ r) := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientDifferenceHom, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeSplitComparison_D]

end IsLocalizingInvariant
end SerrePositivity.InfinityCategories.Derived.Lax

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientVerdierSequence (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.laxQuotientVerdierSequence := _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientVerdierSequence

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientDifferenceHom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientDifferenceHom := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientDifferenceHom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientDifferenceHom_C := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientDifferenceHom_C

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientDifferenceHom_D := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientDifferenceHom_D

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientFiberMiddleIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientFiberMiddleIso := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientFiberMiddleIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientFiberMiddleIso_right := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientFiberMiddleIso_right

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientFiberTriangle := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientFiberTriangle_bottom := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle_bottom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientFiberTriangle_isFiber := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle_isFiber

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientFiberTriangle_right := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientDifferenceHom.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientDifferenceHom.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientFiberMiddleIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientFiberMiddleIso._proof_1
