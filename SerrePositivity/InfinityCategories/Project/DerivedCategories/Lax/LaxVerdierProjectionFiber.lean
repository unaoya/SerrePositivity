module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.KST.LocalizingInvariants.TammeProjectionEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxVerdierInvariantFiber

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
end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax
open _root_.SerrePositivity.KST.LocalizingInvariants
open _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
variable {Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i r)

def laxQuotientProjectionMiddleIso :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle p q i r h hΦ)).square 1 0 ≅
      SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) :=
  hΦ.fiberMiddleIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientVerdierSequence p q i r h) ≪≫ hΦ.tammeProjectionEquivalence p q

def laxQuotientProjectionDifferenceHom : SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) ⟶
    SpectrumHo.obj (value Φ Q) :=
  (hΦ.tammeProjectionEquivalence p q).inv ≫ SpectrumHo.hom (valueMap Φ r)

lemma laxQuotientProjectionMiddleIso_right :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProjectionMiddleIso hΦ) p q i r h).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProjectionDifferenceHom hΦ) p q r =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle p q i r h hΦ)).square ≫
        (hΦ.fiberRightIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientVerdierSequence p q i r h)).hom := by
  change ((hΦ.fiberMiddleIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientVerdierSequence p q i r h)).hom ≫
    (hΦ.tammeProjectionEquivalence p q).hom) ≫
      ((hΦ.tammeProjectionEquivalence p q).inv ≫ _) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact hΦ.fiber_right_naturality (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientVerdierSequence p q i r h)

lemma laxQuotientProjectionDifferenceHom_C :
    SpectrumHo.hom (Binary.inl (value Φ C) (value Φ D)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProjectionDifferenceHom hΦ) p q r =
      SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromC p q)) ≫
        SpectrumHo.hom (valueMap Φ r) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProjectionDifferenceHom, ← Category.assoc, tammeProjectionEquivalence_inv_inl]

lemma laxQuotientProjectionDifferenceHom_D :
    SpectrumHo.hom (Binary.inr (value Φ C) (value Φ D)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProjectionDifferenceHom hΦ) p q r =
      SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromD p q)) ≫
        SpectrumHo.hom (valueMap Φ r) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProjectionDifferenceHom, ← Category.assoc, tammeProjectionEquivalence_inv_inr]

lemma laxQuotientProjectionMiddleIso_bottom_fst :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle p q i r h hΦ)).square ≫
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProjectionMiddleIso hΦ) p q i r h).hom ≫
          SpectrumHo.hom (Binary.fst (value Φ C) (value Φ D)) =
      (hΦ.fiberLeftIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientVerdierSequence p q i r h)).hom ≫
        SpectrumHo.hom (valueMap Φ i) ≫ SpectrumHo.hom (valueMap Φ (laxFst p q)) := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom (hΦ.abstractFiberTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientVerdierSequence p q i r h)).square ≫
    ((hΦ.fiberMiddleIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientVerdierSequence p q i r h)).hom ≫
      (hΦ.tammeProjectionEquivalence p q).hom) ≫ SpectrumHo.hom (Binary.fst _ _) = _
  rw [Category.assoc, tammeProjectionEquivalence_fst]
  rw [← Category.assoc,
    ← hΦ.fiber_bottom_naturality (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientVerdierSequence p q i r h), Category.assoc]
  rfl

lemma laxQuotientProjectionMiddleIso_bottom_snd :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle p q i r h hΦ)).square ≫
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProjectionMiddleIso hΦ) p q i r h).hom ≫
          SpectrumHo.hom (Binary.snd (value Φ C) (value Φ D)) =
      (hΦ.fiberLeftIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientVerdierSequence p q i r h)).hom ≫
        SpectrumHo.hom (valueMap Φ i) ≫ SpectrumHo.hom (valueMap Φ (laxSnd p q)) := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom (hΦ.abstractFiberTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientVerdierSequence p q i r h)).square ≫
    ((hΦ.fiberMiddleIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientVerdierSequence p q i r h)).hom ≫
      (hΦ.tammeProjectionEquivalence p q).hom) ≫ SpectrumHo.hom (Binary.snd _ _) = _
  rw [Category.assoc, tammeProjectionEquivalence_snd]
  rw [← Category.assoc,
    ← hΦ.fiber_bottom_naturality (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientVerdierSequence p q i r h), Category.assoc]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
