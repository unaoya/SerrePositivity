module

public import SerrePositivity.KST.LocalizingInvariants.TammeProjectionEquivalence
public import SerrePositivity.InfinityCategories.Derived.Lax.LaxVerdierInvariantFiber

/-!
概要：d8 の fiber 列の中項を、元の両射影を保つ実積へ同定する。
方針：両射影の積同値で右辺を移し、元の包含と商の作用との整合を保持する。
規約：実 pullback 比較はまだ主張しない。使われ方：抽象 Land–Tamme の二つの脚。
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
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)
  (h : IsVerdierSequence i r)

def laxQuotientProjectionMiddleIso :
    squareHoVertex (hΦ.laxQuotientFiberTriangle p q i r h).square 1 0 ≅
      SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) :=
  hΦ.fiberMiddleIso (laxQuotientVerdierSequence p q i r h) ≪≫ hΦ.tammeProjectionEquivalence p q

def laxQuotientProjectionDifferenceHom : SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) ⟶
    SpectrumHo.obj (value Φ Q) :=
  (hΦ.tammeProjectionEquivalence p q).inv ≫ SpectrumHo.hom (valueMap Φ r)

lemma laxQuotientProjectionMiddleIso_right :
    (hΦ.laxQuotientProjectionMiddleIso p q i r h).hom ≫
        hΦ.laxQuotientProjectionDifferenceHom p q r =
      squareHoRight (hΦ.laxQuotientFiberTriangle p q i r h).square ≫
        (hΦ.fiberRightIso (laxQuotientVerdierSequence p q i r h)).hom := by
  change ((hΦ.fiberMiddleIso (laxQuotientVerdierSequence p q i r h)).hom ≫
    (hΦ.tammeProjectionEquivalence p q).hom) ≫
      ((hΦ.tammeProjectionEquivalence p q).inv ≫ _) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact hΦ.fiber_right_naturality (laxQuotientVerdierSequence p q i r h)

lemma laxQuotientProjectionDifferenceHom_C :
    SpectrumHo.hom (Binary.inl (value Φ C) (value Φ D)) ≫
        hΦ.laxQuotientProjectionDifferenceHom p q r =
      SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromC p q)) ≫
        SpectrumHo.hom (valueMap Φ r) := by
  rw [laxQuotientProjectionDifferenceHom, ← Category.assoc, tammeProjectionEquivalence_inv_inl]

lemma laxQuotientProjectionDifferenceHom_D :
    SpectrumHo.hom (Binary.inr (value Φ C) (value Φ D)) ≫
        hΦ.laxQuotientProjectionDifferenceHom p q r =
      SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromD p q)) ≫
        SpectrumHo.hom (valueMap Φ r) := by
  rw [laxQuotientProjectionDifferenceHom, ← Category.assoc, tammeProjectionEquivalence_inv_inr]

lemma laxQuotientProjectionMiddleIso_bottom_fst :
    squareHoBottom (hΦ.laxQuotientFiberTriangle p q i r h).square ≫
        (hΦ.laxQuotientProjectionMiddleIso p q i r h).hom ≫
          SpectrumHo.hom (Binary.fst (value Φ C) (value Φ D)) =
      (hΦ.fiberLeftIso (laxQuotientVerdierSequence p q i r h)).hom ≫
        SpectrumHo.hom (valueMap Φ i) ≫ SpectrumHo.hom (valueMap Φ (laxFst p q)) := by
  change squareHoBottom (hΦ.abstractFiberTriangle (laxQuotientVerdierSequence p q i r h)).square ≫
    ((hΦ.fiberMiddleIso (laxQuotientVerdierSequence p q i r h)).hom ≫
      (hΦ.tammeProjectionEquivalence p q).hom) ≫ SpectrumHo.hom (Binary.fst _ _) = _
  rw [Category.assoc, tammeProjectionEquivalence_fst]
  rw [← Category.assoc,
    ← hΦ.fiber_bottom_naturality (laxQuotientVerdierSequence p q i r h), Category.assoc]
  rfl

lemma laxQuotientProjectionMiddleIso_bottom_snd :
    squareHoBottom (hΦ.laxQuotientFiberTriangle p q i r h).square ≫
        (hΦ.laxQuotientProjectionMiddleIso p q i r h).hom ≫
          SpectrumHo.hom (Binary.snd (value Φ C) (value Φ D)) =
      (hΦ.fiberLeftIso (laxQuotientVerdierSequence p q i r h)).hom ≫
        SpectrumHo.hom (valueMap Φ i) ≫ SpectrumHo.hom (valueMap Φ (laxSnd p q)) := by
  change squareHoBottom (hΦ.abstractFiberTriangle (laxQuotientVerdierSequence p q i r h)).square ≫
    ((hΦ.fiberMiddleIso (laxQuotientVerdierSequence p q i r h)).hom ≫
      (hΦ.tammeProjectionEquivalence p q).hom) ≫ SpectrumHo.hom (Binary.snd _ _) = _
  rw [Category.assoc, tammeProjectionEquivalence_snd]
  rw [← Category.assoc,
    ← hΦ.fiber_bottom_naturality (laxQuotientVerdierSequence p q i r h), Category.assoc]
  rfl

end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
