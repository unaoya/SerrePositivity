module

public import SerrePositivity.KST.LocalizingInvariants.LaxValueProjectionAxes
public import SerrePositivity.KST.LocalizingInvariants.BinaryAxesEquivalence

/-!
概要：元の両射影を順方向に持つ Tamme の実積同値。
方針：既存の積分裂との合成が両軸を固定するので、全整数 π による同値検出を適用する。
規約：既存の分裂と同じ射だとは仮定しない。使われ方：d8 の元の二射影との整合。
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
  {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

include hΦ in
lemma laxValueProjectionHom_isIso : IsIso (laxValueProjectionHom Φ p q) := by
  let s := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitComparison hΦ) p q
  have hi : IsIso (s.hom ≫ laxValueProjectionHom Φ p q) := by
    apply Binary.isIso_of_axes_fixed
    · rw [← Category.assoc]
      change (SpectrumHo.hom (Binary.inl _ _) ≫ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitComparison hΦ) p q).hom) ≫ _ = _
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitComparison_C, hΦ.laxValueProjectionHom_fromC]
    · rw [← Category.assoc]
      change (SpectrumHo.hom (Binary.inr _ _) ≫ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitComparison hΦ) p q).hom) ≫ _ = _
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitComparison_D, hΦ.laxValueProjectionHom_fromD]
  have h : IsIso (s.inv ≫ (s.hom ≫ laxValueProjectionHom Φ p q)) := inferInstance
  simpa only [Iso.inv_hom_id_assoc] using h

def tammeProjectionEquivalence : SpectrumHo.obj (value Φ (laxCategory p q)) ≅
    SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) := by
  have := hΦ.laxValueProjectionHom_isIso p q
  exact asIso (laxValueProjectionHom Φ p q)

lemma tammeProjectionEquivalence_hom : (hΦ.tammeProjectionEquivalence p q).hom =
    laxValueProjectionHom Φ p q := rfl

lemma tammeProjectionEquivalence_fst : (hΦ.tammeProjectionEquivalence p q).hom ≫
    SpectrumHo.hom (Binary.fst (value Φ C) (value Φ D)) =
      SpectrumHo.hom (valueMap Φ (laxFst p q)) := laxValueProjectionHom_fst Φ p q

lemma tammeProjectionEquivalence_snd : (hΦ.tammeProjectionEquivalence p q).hom ≫
    SpectrumHo.hom (Binary.snd (value Φ C) (value Φ D)) =
      SpectrumHo.hom (valueMap Φ (laxSnd p q)) := laxValueProjectionHom_snd Φ p q

lemma tammeProjectionEquivalence_fromC :
    SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromC p q)) ≫
      (hΦ.tammeProjectionEquivalence p q).hom =
        SpectrumHo.hom (Binary.inl (value Φ C) (value Φ D)) := hΦ.laxValueProjectionHom_fromC p q

lemma tammeProjectionEquivalence_fromD :
    SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromD p q)) ≫
      (hΦ.tammeProjectionEquivalence p q).hom =
        SpectrumHo.hom (Binary.inr (value Φ C) (value Φ D)) := hΦ.laxValueProjectionHom_fromD p q

lemma tammeProjectionEquivalence_inv_inl :
    SpectrumHo.hom (Binary.inl (value Φ C) (value Φ D)) ≫
      (hΦ.tammeProjectionEquivalence p q).inv =
        SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromC p q)) := by
  apply (cancel_mono (hΦ.tammeProjectionEquivalence p q).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, tammeProjectionEquivalence_fromC]

lemma tammeProjectionEquivalence_inv_inr :
    SpectrumHo.hom (Binary.inr (value Φ C) (value Φ D)) ≫
      (hΦ.tammeProjectionEquivalence p q).inv =
        SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromD p q)) := by
  apply (cancel_mono (hΦ.tammeProjectionEquivalence p q).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, tammeProjectionEquivalence_fromD]

end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
