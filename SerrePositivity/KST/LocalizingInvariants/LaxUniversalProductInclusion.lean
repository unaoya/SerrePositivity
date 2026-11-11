module

public import SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductEdgeClasses
public import SerrePositivity.KST.LocalizingInvariants.LaxVerdierProductFiberMap

/-!
概要：実積正方形の下辺は、元の包含と両射影の実 BF の組に一致する。
方針：実積の両射影による外延性で、移送された下辺の類を計算する。
規約：元の両射影を保持。使われ方：四辺固定の実積 pullback 正方形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct
variable {Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i r)

lemma inclusion_projection : SpectrumHo.hom (valueMap Φ i) ≫
    (hΦ.tammeProjectionEquivalence p q).hom =
      SpectrumHo.hom (IsLocalizingInvariant.laxQuotientProductInclusion (Φ := Φ) p q i) := by
  apply Binary.ho_hom_ext
  · rw [Category.assoc, hΦ.tammeProjectionEquivalence_fst]
    symm
    rw [← SpectrumHo.hom_comp, IsLocalizingInvariant.laxQuotientProductInclusion,
      Binary.lift_fst, SpectrumHo.hom_comp]
  · rw [Category.assoc, hΦ.tammeProjectionEquivalence_snd]
    symm
    rw [← SpectrumHo.hom_comp, IsLocalizingInvariant.laxQuotientProductInclusion,
      Binary.lift_snd, SpectrumHo.hom_comp]

lemma bottom_native_arrow : Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoBottom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.square hΦ p q i r h)) =
    Arrow.mk (SpectrumHo.hom
      (IsLocalizingInvariant.laxQuotientProductInclusion (Φ := Φ) p q i)) :=
  (bottom_arrow hΦ p q i r h).trans (congrArg Arrow.mk (inclusion_projection hΦ p q i))

end SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct
