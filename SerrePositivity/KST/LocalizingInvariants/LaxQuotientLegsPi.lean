module

public import SerrePositivity.KST.LocalizingInvariants.LaxQuotientDifferencePi
public import SerrePositivity.KST.LocalizingInvariants.LaxVerdierProductFiberMap

/-!
概要：元の包含から出る二脚は、一般商 Q の全整数 π で可換する。
方針：実包含・差の h Sp の零合成を π に写し、証明済みの差の符号を展開する。
規約：実 cospan の coherent な可換比較の代用にはしない。使われ方：d8 の π 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
variable {Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i r)

include h in
lemma laxQuotientProductInclusion_pi_zero (j : ℤ) (a : valueHomotopyGroup Φ A j) :
    homotopyMap ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductMap hΦ) p q r) j
      (homotopyMap (laxQuotientProductInclusion p q i) j a) = 1 := by
  have he : SpectrumHo.hom (laxQuotientProductInclusion p q i ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductMap hΦ) p q r) = SpectrumHo.hom (0 : value Φ A ⟶ value Φ Q) := by
    rw [SpectrumHo.hom_comp, hΦ.laxQuotientProductInclusion_comp_map p q i r h,
      SpectrumHo.hom_zero]
  simpa only [homotopyMap_comp, MonoidHom.comp_apply, Binary.map_zero,
    MonoidHom.one_apply] using
      DFunLike.congr_fun (SpectrumHo.homotopyMap_eq_of_hom_eq _ _ he j) a

include hΦ h in
lemma laxQuotientLegs_pi_commute (j : ℤ) (a : valueHomotopyGroup Φ A j) :
    valueHomotopyMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg p q r) j
        (valueHomotopyMap Φ (laxFst p q) j (valueHomotopyMap Φ i j a)) =
      valueHomotopyMap Φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientDLeg p q r) j
        (valueHomotopyMap Φ (laxSnd p q) j (valueHomotopyMap Φ i j a)) := by
  have hf : homotopyMap (Binary.fst (value Φ C) (value Φ D)) j
      (homotopyMap (laxQuotientProductInclusion p q i) j a) =
    valueHomotopyMap Φ (laxFst p q) j (valueHomotopyMap Φ i j a) := by
    rw [Binary.map_comp_apply, laxQuotientProductInclusion, Binary.lift_fst]
    exact DFunLike.congr_fun (homotopyMap_comp _ _ j) a
  have hs : homotopyMap (Binary.snd (value Φ C) (value Φ D)) j
      (homotopyMap (laxQuotientProductInclusion p q i) j a) =
    valueHomotopyMap Φ (laxSnd p q) j (valueHomotopyMap Φ i j a) := by
    rw [Binary.map_comp_apply, laxQuotientProductInclusion, Binary.lift_snd]
    exact DFunLike.congr_fun (homotopyMap_comp _ _ j) a
  have hz := (hΦ.laxQuotientProductMap_pi_formula p q r j
    (homotopyMap (laxQuotientProductInclusion p q i) j a)).symm.trans
      (hΦ.laxQuotientProductInclusion_pi_zero p q i r h j a)
  rw [hf, hs] at hz
  exact inv_mul_eq_one.mp hz

end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
