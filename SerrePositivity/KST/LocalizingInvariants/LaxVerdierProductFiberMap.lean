module

public import SerrePositivity.InfinityCategories.Derived.Lax.LaxVerdierProductFiberLegs

/-!
概要：元の包含・二射影の組を実 BF 射に束ね、product fiber の下辺と同定する。
方針：両射影の式で射の類を決定し、指定右辺の端点輸送で合成零を導く。
規約：整数 π の一致だけで射を同定しない。使われ方：元の三対象の fiber 列。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
local instance productFiberMapSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
variable {Φ : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i r)

def laxQuotientProductInclusion : value Φ A ⟶ Binary.obj (value Φ C) (value Φ D) :=
  Binary.lift (valueMap Φ i ≫ valueMap Φ (laxFst p q))
    (valueMap Φ i ≫ valueMap Φ (laxSnd p q))

lemma laxQuotientProductFiber_bottom_map :
    ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductFiberLeftIso hΦ) p q i r h).inv ≫
        squareHoBottom (hΦ.laxQuotientProductFiberSquare p q i r h).square ≫
          ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductFiberMiddleIso hΦ) p q i r h).hom =
      SpectrumHo.hom (laxQuotientProductInclusion p q i) := by
  apply Binary.ho_hom_ext
  · rw [Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductFiber_bottom_fst,
      Iso.inv_hom_id_assoc]
    simp only [laxQuotientProductInclusion, ← SpectrumHo.hom_comp, Binary.lift_fst]
  · rw [Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductFiber_bottom_snd,
      Iso.inv_hom_id_assoc]
    simp only [laxQuotientProductInclusion, ← SpectrumHo.hom_comp, Binary.lift_snd]

lemma laxQuotientProductFiber_right_map :
    ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductFiberMiddleIso hΦ) p q i r h).hom ≫
        SpectrumHo.hom ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductMap hΦ) p q r) =
      squareHoRight (hΦ.laxQuotientProductFiberSquare p q i r h).square ≫
        ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductFiberRightIso hΦ) p q i r h).hom := by
  have he : (squareRightArrow (hΦ.laxQuotientProductFiberSquare p q i r h).square).edge =
      (coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductMap hΦ) p q r)).edge := by
    rw [squareRightArrow_edge,
      (hΦ.laxQuotientProductFiberSquare p q i r h).right_edge]
    exact SSet.yonedaEquiv.apply_symm_apply _
  exact (FiberModel.homMk_transport _ _
    ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductFiber_middle_vertex hΦ) p q i r h)
    ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductFiber_right_vertex hΦ) p q i r h) he).symm

include h in
lemma laxQuotientProductInclusion_comp_map :
    SpectrumHo.hom (laxQuotientProductInclusion p q i) ≫
      SpectrumHo.hom ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductMap hΦ) p q r) = 0 := by
  rw [← hΦ.laxQuotientProductFiber_bottom_map p q i r h, Category.assoc,
    Category.assoc, laxQuotientProductFiber_right_map]
  rw [← Category.assoc (squareHoBottom _) (squareHoRight _),
    (hΦ.laxQuotientProductFiberSquare p q i r h).toZeroTriangle.homMk_comp_eq_zero,
    CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]

end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
