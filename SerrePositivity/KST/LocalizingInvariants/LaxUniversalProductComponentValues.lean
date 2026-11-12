module

public import SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductComponents

/-!
概要：実積への移送の四成分は、元の恒等と二つの Tamme 射影同値そのものである。
方針：端点の等号による輸送を Arrow の等号で除く。
規約：二次の整合を変更しない。使われ方：移送した実 pullback 正方形の四辺の照合。
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

lemma component00_arrow : Arrow.mk (component hΦ p q i r h 0 0) =
    Arrow.mk (𝟙 (SpectrumHo.obj (value Φ A))) := by
  rw [component_arrow]
  change Arrow.mk (eqToHom (congrArg HomotopyCategory.mk
    (LaxUniversalValue.vertex00 Φ p q i r h))) = _
  simpa only [Category.comp_id] using arrow_mk_eqToHom_comp
    (congrArg HomotopyCategory.mk (LaxUniversalValue.vertex00 Φ p q i r h))
    (𝟙 (SpectrumHo.obj (value Φ A)))

lemma component01_arrow : Arrow.mk (component hΦ p q i r h 0 1) =
    Arrow.mk (𝟙 (SpectrumHo.obj (value Φ Q))) := by
  rw [component_arrow]
  change Arrow.mk (eqToHom (congrArg HomotopyCategory.mk
    (LaxUniversalValue.vertex01 Φ p q i r h))) = _
  simpa only [Category.comp_id] using arrow_mk_eqToHom_comp
    (congrArg HomotopyCategory.mk (LaxUniversalValue.vertex01 Φ p q i r h))
    (𝟙 (SpectrumHo.obj (value Φ Q)))

lemma component10_arrow : Arrow.mk (component hΦ p q i r h 1 0) =
    Arrow.mk (hΦ.tammeProjectionEquivalence p q).hom := by
  rw [component_arrow]
  change Arrow.mk (eqToHom (congrArg HomotopyCategory.mk
    (LaxUniversalValue.vertex10 Φ p q i r h)) ≫ (hΦ.tammeProjectionEquivalence p q).hom) = _
  exact arrow_mk_eqToHom_comp _ _

lemma component11_arrow : Arrow.mk (component hΦ p q i r h 1 1) =
    Arrow.mk (hΦ.tammeProjectionEquivalence (𝟙 Q) (𝟙 Q)).hom := by
  rw [component_arrow]
  change Arrow.mk (eqToHom (congrArg HomotopyCategory.mk
    (LaxUniversalValue.vertex11 Φ p q i r h)) ≫
      (hΦ.tammeProjectionEquivalence (𝟙 Q) (𝟙 Q)).hom) = _
  exact arrow_mk_eqToHom_comp _ _

end SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct
