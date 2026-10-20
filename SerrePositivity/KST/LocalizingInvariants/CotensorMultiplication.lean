module

public import SerrePositivity.KST.LocalizingInvariants.CotensorAddition
public import SerrePositivity.KST.LocalizingInvariants.SpectrumBinaryMaps
public import SerrePositivity.KST.LocalizingInvariants.SpectrumComponentClass

/-!
概要：Kan 円 cotensor には両軸で単位となる実 BF 積の射がある。
方針：二項積の二つの射影の和の代表を選び、前合成自然性で軸の法則を検査する。
規約：単位則は h Sp の実際の等式。使われ方：coherent な切断の積比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
open SpectrumMappingAcyclic
namespace SerrePositivity.KST.LocalizingInvariants.CotensorClasses

variable (Z : OmegaSpectrum.{u})

/-- 元の BF 二項積から cotensor への、二射影の和を表す射。 -/
def multiplication : Binary.obj (target Z) (target Z) ⟶ target Z :=
  add (Z := Z) (Binary.fst (target Z) (target Z)) (Binary.snd (target Z) (target Z))

lemma multiplication_left_component :
    component (Binary.inl (target Z) (target Z) ≫ multiplication Z) = component (𝟙 (target Z)) := by
  have h := component_pre_add (Binary.inl (target Z) (target Z))
    (Binary.fst (target Z) (target Z)) (Binary.snd (target Z) (target Z))
  simpa only [multiplication, Binary.inl_fst, Binary.inl_snd, component_add_zero] using h

lemma multiplication_right_component :
    component (Binary.inr (target Z) (target Z) ≫ multiplication Z) = component (𝟙 (target Z)) := by
  have h := component_pre_add (Binary.inr (target Z) (target Z))
    (Binary.fst (target Z) (target Z)) (Binary.snd (target Z) (target Z))
  simpa only [multiplication, Binary.inr_fst, Binary.inr_snd, component_zero_add] using h

lemma multiplication_left_hom :
    SpectrumHo.hom (Binary.inl (target Z) (target Z)) ≫ SpectrumHo.hom (multiplication Z) =
      𝟙 (SpectrumHo.obj (target Z)) := by
  rw [← SpectrumHo.hom_comp]
  exact (SpectrumHo.hom_eq_of_component_eq _ _ (multiplication_left_component Z)).trans
    (SpectrumHo.hom_id _)

lemma multiplication_right_hom :
    SpectrumHo.hom (Binary.inr (target Z) (target Z)) ≫ SpectrumHo.hom (multiplication Z) =
      𝟙 (SpectrumHo.obj (target Z)) := by
  rw [← SpectrumHo.hom_comp]
  exact (SpectrumHo.hom_eq_of_component_eq _ _ (multiplication_right_component Z)).trans
    (SpectrumHo.hom_id _)

end SerrePositivity.KST.LocalizingInvariants.CotensorClasses
