module

public import SerrePositivity.InfinityCategories.Derived.Lax.LaxVerdierProjectionFiber
public import SerrePositivity.InfinityCategories.Derived.Lax.LaxVerdierReflectiveCompatibility

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
variable {Φ : StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)

def tammeProjectionCorrection : SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) ≅
    SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) :=
  hΦ.tammeSplitComparison p q ≪≫ hΦ.tammeProjectionEquivalence p q

lemma tammeProjectionCorrection_inl : SpectrumHo.hom (Binary.inl (value Φ C) (value Φ D)) ≫
    (hΦ.tammeProjectionCorrection p q).hom =
      SpectrumHo.hom (Binary.inl (value Φ C) (value Φ D)) := by
  rw [tammeProjectionCorrection, Iso.trans_hom, ← Category.assoc,
    tammeSplitComparison_C, tammeProjectionEquivalence_fromC]

lemma tammeProjectionCorrection_inr : SpectrumHo.hom (Binary.inr (value Φ C) (value Φ D)) ≫
    (hΦ.tammeProjectionCorrection p q).hom =
      SpectrumHo.hom (Binary.inr (value Φ C) (value Φ D)) := by
  rw [tammeProjectionCorrection, Iso.trans_hom, ← Category.assoc,
    tammeSplitComparison_D, tammeProjectionEquivalence_fromD]

lemma tammeProjectionCorrection_fst : (hΦ.tammeProjectionCorrection p q).hom ≫
    SpectrumHo.hom (Binary.fst (value Φ C) (value Φ D)) =
      SpectrumHo.hom (Binary.fst (value Φ C) (value Φ D)) := by
  rw [tammeProjectionCorrection, Iso.trans_hom, Category.assoc,
    tammeProjectionEquivalence_fst, tammeSplitComparison_projection]

lemma laxQuotientProjectionCorrection_right (r : ExactMap (laxCategory p q) Q) :
    (hΦ.tammeProjectionCorrection p q).hom ≫ hΦ.laxQuotientProjectionDifferenceHom p q r =
      hΦ.laxQuotientDifferenceHom p q r := by
  rw [tammeProjectionCorrection, Iso.trans_hom, laxQuotientProjectionDifferenceHom,
    laxQuotientDifferenceHom, Category.assoc, Iso.hom_inv_id_assoc]

lemma laxQuotientProjectionCorrection_middle (i : ExactMap A (laxCategory p q))
    (r : ExactMap (laxCategory p q) Q) (h : IsVerdierSequence i r) :
    (hΦ.laxQuotientFiberMiddleIso p q i r h).hom ≫ (hΦ.tammeProjectionCorrection p q).hom =
      (hΦ.laxQuotientProjectionMiddleIso p q i r h).hom := by
  change ((hΦ.fiberMiddleIso (laxQuotientVerdierSequence p q i r h)).hom ≫
    (hΦ.tammeSplitComparison p q).inv) ≫
      ((hΦ.tammeSplitComparison p q).hom ≫ (hΦ.tammeProjectionEquivalence p q).hom) = _
  rw [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
