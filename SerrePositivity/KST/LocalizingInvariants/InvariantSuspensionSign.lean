module

public import SerrePositivity.KST.LocalizingInvariants.IdentityLaxInvariantDiagonal
public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceShiftAxes
public import SerrePositivity.KST.LocalizingInvariants.SpectrumBinaryGroups

/-!
概要：局所化不変量が入力圏の suspension に誘導する全整数 π の作用は逆元。
方針：恒等矢印の対角の零化を、二軸による積表示と群準同型性で展開する。
規約：Sp の安定性や h Sp の加法性を仮定しない。使われ方：d8 の差の符号。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.IdentityLax
variable {Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})
  (hΦ : IsLocalizingInvariant Φ)

def difference : Binary.obj (value Φ A) (value Φ A) ⟶ value Φ A :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductMap hΦ) (𝟙 A) (𝟙 A) (exactLaxDifference (𝟙 A) (𝟙 A))

lemma difference_C (j : ℤ) (a : valueHomotopyGroup Φ A j) :
    homotopyMap (difference A hΦ) j (homotopyMap (Binary.inl _ _) j a) =
      valueHomotopyMap Φ (SuspensionExact.exactMap A) j a := by
  have hi : SpectrumHo.hom (valueMap Φ (𝟙 A)) = 𝟙 _ := (stableValueFunctor Φ).map_id A
  have he : SpectrumHo.hom (Binary.inl (value Φ A) (value Φ A) ≫ difference A hΦ) =
      SpectrumHo.hom (valueMap Φ (SuspensionExact.exactMap A)) := by
    rw [SpectrumHo.hom_comp, difference, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductMap_hom,
      IsLocalizingInvariant.laxQuotientProjectionDifferenceHom_cofiber_C, hi, Category.id_comp]
  have hp := SpectrumHo.homotopyMap_eq_of_hom_eq _ _ he j
  simpa only [homotopyMap_comp, MonoidHom.comp_apply, valueHomotopyMap] using
    DFunLike.congr_fun hp a

lemma difference_D (j : ℤ) (a : valueHomotopyGroup Φ A j) :
    homotopyMap (difference A hΦ) j (homotopyMap (Binary.inr _ _) j a) = a := by
  have hi : SpectrumHo.hom (valueMap Φ (𝟙 A)) = 𝟙 _ := (stableValueFunctor Φ).map_id A
  have he : SpectrumHo.hom (Binary.inr (value Φ A) (value Φ A) ≫ difference A hΦ) =
      SpectrumHo.hom (𝟙 (value Φ A)) := by
    rw [SpectrumHo.hom_comp, difference, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductMap_hom,
      IsLocalizingInvariant.laxQuotientProjectionDifferenceHom_cofiber_D, hi, SpectrumHo.hom_id]
  have hp := SpectrumHo.homotopyMap_eq_of_hom_eq _ _ he j
  simpa only [homotopyMap_comp, MonoidHom.comp_apply, homotopyMap_id,
    MonoidHom.id_apply] using DFunLike.congr_fun hp a

lemma difference_diagonal (j : ℤ) (a : valueHomotopyGroup Φ A j) :
    homotopyMap (difference A hΦ) j
      (homotopyMap (Binary.lift (𝟙 (value Φ A)) (𝟙 (value Φ A))) j a) = 1 := by
  have he : SpectrumHo.hom (Binary.lift (𝟙 (value Φ A)) (𝟙 (value Φ A)) ≫ difference A hΦ) =
      SpectrumHo.hom (0 : value Φ A ⟶ value Φ A) := by
    rw [SpectrumHo.hom_comp, difference, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductMap_hom,
      productDiagonal_difference_zero, SpectrumHo.hom_zero]
  have hp := SpectrumHo.homotopyMap_eq_of_hom_eq _ _ he j
  simpa only [homotopyMap_comp, MonoidHom.comp_apply, Binary.map_zero,
    MonoidHom.one_apply] using DFunLike.congr_fun hp a

end IdentityLax

namespace IsLocalizingInvariant
variable {Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})

include hΦ in
lemma suspension_pi_inv (j : ℤ) (a : valueHomotopyGroup Φ A j) :
    valueHomotopyMap Φ (SuspensionExact.exactMap A) j a = a⁻¹ := by
  have hz := IdentityLax.difference_diagonal A hΦ j a
  rw [Binary.lift_map, homotopyMap_id, MonoidHom.id_apply, map_mul,
    IdentityLax.difference_C, IdentityLax.difference_D] at hz
  exact eq_inv_iff_mul_eq_one.mpr hz

end IsLocalizingInvariant
end SerrePositivity.KST.LocalizingInvariants
