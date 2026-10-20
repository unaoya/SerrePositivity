module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumMultiplication
public import SerrePositivity.KST.LocalizingInvariants.SpectrumBinaryGroups

/-!
概要：構成した BF 積の射は整数 π で群の積を与える。
方針：両軸の単位則と、二項積の群の軸による表示を使う。
規約：標的変数の演算の自然性を仮定しない。使われ方：分裂比較の整数 π 同型性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.Multiplication

variable (X : OmegaSpectrum.{u})

lemma left_map (j : ℤ) (a : homotopyGroup X j) :
    homotopyMap (map X) j (homotopyMap (Binary.inl X X) j a) = a := by
  have hh : SpectrumHo.hom (Binary.inl X X ≫ map X) = SpectrumHo.hom (𝟙 X) :=
    (SpectrumHo.hom_comp _ _).trans ((left_hom X).trans (SpectrumHo.hom_id X).symm)
  have hp := SpectrumHo.homotopyMap_eq_of_hom_eq _ _ hh j
  simpa only [homotopyMap_comp, MonoidHom.comp_apply, homotopyMap_id, MonoidHom.id_apply] using
    DFunLike.congr_fun hp a

lemma right_map (j : ℤ) (a : homotopyGroup X j) :
    homotopyMap (map X) j (homotopyMap (Binary.inr X X) j a) = a := by
  have hh : SpectrumHo.hom (Binary.inr X X ≫ map X) = SpectrumHo.hom (𝟙 X) :=
    (SpectrumHo.hom_comp _ _).trans ((right_hom X).trans (SpectrumHo.hom_id X).symm)
  have hp := SpectrumHo.homotopyMap_eq_of_hom_eq _ _ hh j
  simpa only [homotopyMap_comp, MonoidHom.comp_apply, homotopyMap_id, MonoidHom.id_apply] using
    DFunLike.congr_fun hp a

/-- 元の積の射の全整数 π での作用。 -/
lemma map_apply (j : ℤ) (a : homotopyGroup (Binary.obj X X) j) :
    homotopyMap (map X) j a =
      homotopyMap (Binary.fst X X) j a * homotopyMap (Binary.snd X X) j a := by
  have h := congrArg (fun b ↦ homotopyMap (map X) j b) (Binary.axes X X j a)
  simpa only [map_mul, left_map, right_map] using h.symm

lemma pair_apply {A : OmegaSpectrum.{u}} (f g : A ⟶ X) (j : ℤ)
    (a : homotopyGroup A j) :
    homotopyMap (Binary.lift f g ≫ map X) j a = homotopyMap f j a * homotopyMap g j a := by
  rw [homotopyMap_comp, MonoidHom.comp_apply, map_apply, Binary.map_comp_apply,
    Binary.lift_fst, Binary.map_comp_apply, Binary.lift_snd]

end SerrePositivity.KST.LocalizingInvariants.Multiplication
