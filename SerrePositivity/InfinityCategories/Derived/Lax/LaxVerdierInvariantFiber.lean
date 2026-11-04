module

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
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)
  (h : IsVerdierSequence i r)

def laxQuotientVerdierSequence : VerdierSequence.{u} where
  left := A
  middle := laxCategory p q
  right := Q
  inclusion := i
  projection := r
  isVerdier := h

namespace IsLocalizingInvariant
variable {Φ : StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)

def laxQuotientFiberTriangle : ZeroTriangle Sp.{u} :=
  hΦ.abstractFiberTriangle (laxQuotientVerdierSequence p q i r h)

lemma laxQuotientFiberTriangle_isFiber : IsFiberSequence (hΦ.laxQuotientFiberTriangle p q i r h) :=
  hΦ.abstractFiberTriangle_isFiber (laxQuotientVerdierSequence p q i r h)

lemma laxQuotientFiberTriangle_bottom :
    squareBottomEdge ≫ (hΦ.laxQuotientFiberTriangle p q i r h).square =
      SSet.yonedaEquiv.symm (Φ.app (Opposite.op ⦋1⦌) (stableArrow i).edge) :=
  hΦ.abstractFiberTriangle_bottom (laxQuotientVerdierSequence p q i r h)

lemma laxQuotientFiberTriangle_right :
    squareRightEdge ≫ (hΦ.laxQuotientFiberTriangle p q i r h).square =
      SSet.yonedaEquiv.symm (Φ.app (Opposite.op ⦋1⦌) (stableArrow r).edge) :=
  hΦ.abstractFiberTriangle_right (laxQuotientVerdierSequence p q i r h)

def laxQuotientFiberMiddleIso :
    squareHoVertex (hΦ.laxQuotientFiberTriangle p q i r h).square 1 0 ≅
      SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) :=
  hΦ.fiberMiddleIso (laxQuotientVerdierSequence p q i r h) ≪≫ hΦ.tammeSplitEquivalence p q

def laxQuotientDifferenceHom : SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) ⟶
    SpectrumHo.obj (value Φ Q) :=
  (hΦ.tammeSplitComparison p q).hom ≫ SpectrumHo.hom (valueMap Φ r)

lemma laxQuotientFiberMiddleIso_right :
    (hΦ.laxQuotientFiberMiddleIso p q i r h).hom ≫ hΦ.laxQuotientDifferenceHom p q r =
      squareHoRight (hΦ.laxQuotientFiberTriangle p q i r h).square ≫
        (hΦ.fiberRightIso (laxQuotientVerdierSequence p q i r h)).hom := by
  change ((hΦ.fiberMiddleIso (laxQuotientVerdierSequence p q i r h)).hom ≫
    (hΦ.tammeSplitComparison p q).inv) ≫ ((hΦ.tammeSplitComparison p q).hom ≫ _) = _
  rw [Category.assoc, Iso.inv_hom_id_assoc]
  exact hΦ.fiber_right_naturality (laxQuotientVerdierSequence p q i r h)

lemma laxQuotientDifferenceHom_C : SpectrumHo.hom (Binary.inl (value Φ C) (value Φ D)) ≫
    hΦ.laxQuotientDifferenceHom p q r =
      SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromC p q)) ≫
        SpectrumHo.hom (valueMap Φ r) := by
  rw [laxQuotientDifferenceHom, ← Category.assoc, tammeSplitComparison_C]

lemma laxQuotientDifferenceHom_D : SpectrumHo.hom (Binary.inr (value Φ C) (value Φ D)) ≫
    hΦ.laxQuotientDifferenceHom p q r =
      SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromD p q)) ≫
        SpectrumHo.hom (valueMap Φ r) := by
  rw [laxQuotientDifferenceHom, ← Category.assoc, tammeSplitComparison_D]

end IsLocalizingInvariant
end SerrePositivity.KST.LocalizingInvariants
