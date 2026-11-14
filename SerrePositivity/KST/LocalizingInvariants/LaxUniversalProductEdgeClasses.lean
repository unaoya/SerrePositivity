module

public import SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductComponentValues
public import SerrePositivity.KST.LocalizingInvariants.LaxUniversalValueEdges
public import SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductMap
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.ArrowCompositionCancellation

/-!
概要：実積への移送後の四辺を、元の BF 値・実積射・対角に端点も含めて照合する。
方針：全図式の自然性と指定頂点成分を使い、右辺は実積同値で相殺する。
規約：整数 π の一致は使わない。使われ方：正方形の四辺を固定する境界変形。
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

lemma bottom_arrow : Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.square hΦ p q i r h)) =
    Arrow.mk (SpectrumHo.hom (valueMap Φ i) ≫ (hΦ.tammeProjectionEquivalence p q).hom) := by
  have hn := congrArg Arrow.mk (bottom_naturality hΦ p q i r h)
  have hl := arrow_mk_comp_congr (LaxUniversalValue.bottom_arrow Φ p q i r h)
    (component10_arrow hΦ p q i r h)
  have hr := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrow_mk_comp_of_any_identity (component hΦ p q i r h 0 0)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.square hΦ p q i r h)) (component00_arrow hΦ p q i r h)
  exact hr.symm.trans (hn.symm.trans hl)

lemma left_arrow : Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoLeft (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.square hΦ p q i r h)) =
    Arrow.mk (SpectrumHo.hom (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.kernelMap p q i r))) := by
  have hn := congrArg Arrow.mk (left_naturality hΦ p q i r h)
  have hl := arrow_mk_comp_congr (LaxUniversalValue.left_arrow Φ p q i r h)
    (component01_arrow hΦ p q i r h)
  have hr := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrow_mk_comp_of_any_identity (component hΦ p q i r h 0 0)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoLeft (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.square hΦ p q i r h)) (component00_arrow hΦ p q i r h)
  have hh := hr.symm.trans (hn.symm.trans hl)
  simpa only [Category.comp_id] using hh

lemma top_arrow : Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoTop (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.square hΦ p q i r h)) =
    Arrow.mk (SpectrumHo.hom (Binary.lift (𝟙 (value Φ Q)) (𝟙 (value Φ Q)))) := by
  have hn := congrArg Arrow.mk (top_naturality hΦ p q i r h)
  have hl := arrow_mk_comp_congr (LaxUniversalValue.top_arrow Φ p q i r h)
    (component11_arrow hΦ p q i r h)
  have hr := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrow_mk_comp_of_any_identity (component hΦ p q i r h 0 1)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoTop (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.square hΦ p q i r h)) (component01_arrow hΦ p q i r h)
  exact hr.symm.trans (hn.symm.trans hl) |>.trans
    (congrArg Arrow.mk (IdentityLax.valueDiagonal_product Q hΦ))

lemma right_arrow : Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.square hΦ p q i r h)) =
    Arrow.mk (SpectrumHo.hom (legMap (Φ := Φ) p q r)) := by
  have hn := congrArg Arrow.mk (right_naturality hΦ p q i r h)
  have hl := arrow_mk_comp_congr (LaxUniversalValue.right_arrow Φ p q i r h)
    (component11_arrow hΦ p q i r h)
  have hfg := hn.symm.trans hl |>.trans (congrArg Arrow.mk (value_projection_comm hΦ p q r))
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrow_mk_cancel_comp_left (component10_arrow hΦ p q i r h) hfg

end SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct
