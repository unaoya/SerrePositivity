module

public import SerrePositivity.KST.LocalizingInvariants.InvariantSuspensionSign
public import SerrePositivity.KST.LocalizingInvariants.LaxQuotientShiftLegs

/-!
概要：一般商の実 BF 差は、全整数 π で C 脚の逆元と D 脚の積を与える。
方針：shift を含む二軸の h Sp の等式を π へ移し、suspension の負号で展開する。
規約：二脚は元の完全関手から定義したもの。使われ方：d8 の実 pullback 比較。
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
variable {Φ : StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (r : ExactMap (laxCategory p q) Q)

lemma laxQuotientProductMap_pi_C (j : ℤ) (a : valueHomotopyGroup Φ C j) :
    homotopyMap (hΦ.laxQuotientProductMap p q r) j
        (homotopyMap (Binary.inl (value Φ C) (value Φ D)) j a) =
      (valueHomotopyMap Φ (laxQuotientCLeg p q r) j a)⁻¹ := by
  have he : SpectrumHo.hom (Binary.inl (value Φ C) (value Φ D) ≫
      hΦ.laxQuotientProductMap p q r) =
    SpectrumHo.hom (valueMap Φ (laxQuotientCLeg p q r) ≫
      valueMap Φ (SuspensionExact.exactMap Q)) := by
    rw [SpectrumHo.hom_comp, SpectrumHo.hom_comp, laxQuotientProductMap_hom,
      laxQuotientProjectionDifferenceHom_shift_C]
  have hp := DFunLike.congr_fun (SpectrumHo.homotopyMap_eq_of_hom_eq _ _ he j) a
  simp only [homotopyMap_comp, MonoidHom.comp_apply] at hp
  have hs := hΦ.suspension_pi_inv Q j (valueHomotopyMap Φ (laxQuotientCLeg p q r) j a)
  change homotopyMap (valueMap Φ (SuspensionExact.exactMap Q)) j
    (homotopyMap (valueMap Φ (laxQuotientCLeg p q r)) j a) =
      (valueHomotopyMap Φ (laxQuotientCLeg p q r) j a)⁻¹ at hs
  exact hp.trans hs

lemma laxQuotientProductMap_pi_D (j : ℤ) (a : valueHomotopyGroup Φ D j) :
    homotopyMap (hΦ.laxQuotientProductMap p q r) j
        (homotopyMap (Binary.inr (value Φ C) (value Φ D)) j a) =
      valueHomotopyMap Φ (laxQuotientDLeg p q r) j a := by
  have he : SpectrumHo.hom (Binary.inr (value Φ C) (value Φ D) ≫
      hΦ.laxQuotientProductMap p q r) = SpectrumHo.hom (valueMap Φ (laxQuotientDLeg p q r)) := by
    rw [SpectrumHo.hom_comp, laxQuotientProductMap_hom,
      laxQuotientProjectionDifferenceHom_shift_D]
  simpa only [homotopyMap_comp, MonoidHom.comp_apply, valueHomotopyMap] using
    DFunLike.congr_fun (SpectrumHo.homotopyMap_eq_of_hom_eq _ _ he j) a

lemma laxQuotientProductMap_pi_formula (j : ℤ)
    (a : homotopyGroup (Binary.obj (value Φ C) (value Φ D)) j) :
    homotopyMap (hΦ.laxQuotientProductMap p q r) j a =
      (valueHomotopyMap Φ (laxQuotientCLeg p q r) j
        (homotopyMap (Binary.fst (value Φ C) (value Φ D)) j a))⁻¹ *
      valueHomotopyMap Φ (laxQuotientDLeg p q r) j
        (homotopyMap (Binary.snd (value Φ C) (value Φ D)) j a) := by
  have h := congrArg (homotopyMap (hΦ.laxQuotientProductMap p q r) j)
    (Binary.axes (value Φ C) (value Φ D) j a)
  rw [map_mul, laxQuotientProductMap_pi_C, laxQuotientProductMap_pi_D] at h
  exact h.symm

end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
