module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxVerdierProjectionFiber
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxVerdierReflectiveCompatibility

/-!
概要：両射影を持つ d8 の積比較と、既存の Tamme 分裂による比較との整合。
方針：同じ実積の座標変換を明示し、両軸・第一射影・元の商への作用を保つ。
規約：二つの比較を無根拠に等置しない。使われ方：充満忠実右随伴の場合との接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
variable {Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

def tammeProjectionCorrection : SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) ≅
    SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitComparison hΦ) p q ≪≫ hΦ.tammeProjectionEquivalence p q

lemma tammeProjectionCorrection_inl : SpectrumHo.hom (Binary.inl (value Φ C) (value Φ D)) ≫
    (hΦ.tammeProjectionCorrection p q).hom =
      SpectrumHo.hom (Binary.inl (value Φ C) (value Φ D)) := by
  rw [tammeProjectionCorrection, Iso.trans_hom, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitComparison_C, tammeProjectionEquivalence_fromC]

lemma tammeProjectionCorrection_inr : SpectrumHo.hom (Binary.inr (value Φ C) (value Φ D)) ≫
    (hΦ.tammeProjectionCorrection p q).hom =
      SpectrumHo.hom (Binary.inr (value Φ C) (value Φ D)) := by
  rw [tammeProjectionCorrection, Iso.trans_hom, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitComparison_D, tammeProjectionEquivalence_fromD]

lemma tammeProjectionCorrection_fst : (hΦ.tammeProjectionCorrection p q).hom ≫
    SpectrumHo.hom (Binary.fst (value Φ C) (value Φ D)) =
      SpectrumHo.hom (Binary.fst (value Φ C) (value Φ D)) := by
  rw [tammeProjectionCorrection, Iso.trans_hom, Category.assoc,
    tammeProjectionEquivalence_fst, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitComparison_projection]

lemma laxQuotientProjectionCorrection_right (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q) :
    (hΦ.tammeProjectionCorrection p q).hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProjectionDifferenceHom hΦ) p q r =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.IsLocalizingInvariant.laxQuotientDifferenceHom p q r hΦ) := by
  rw [tammeProjectionCorrection, Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProjectionDifferenceHom,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.IsLocalizingInvariant.laxQuotientDifferenceHom, Category.assoc, Iso.hom_inv_id_assoc]

lemma laxQuotientProjectionCorrection_middle (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A (laxCategory p q))
    (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q) (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i r) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.IsLocalizingInvariant.laxQuotientFiberMiddleIso p q i r h hΦ)).hom ≫ (hΦ.tammeProjectionCorrection p q).hom =
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProjectionMiddleIso hΦ) p q i r h).hom := by
  change ((hΦ.fiberMiddleIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientVerdierSequence p q i r h)).hom ≫
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitComparison hΦ) p q).inv) ≫
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitComparison hΦ) p q).hom ≫ (hΦ.tammeProjectionEquivalence p q).hom) = _
  rw [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
