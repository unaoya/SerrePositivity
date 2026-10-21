module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumBinaryGroups
public import SerrePositivity.KST.LocalizingInvariants.SpectrumHomotopyFunctor
public import SerrePositivity.KST.Spectra.SpectrumIntegerHomotopyDetection

/-!
概要：二項積の両軸を固定する h Sp の自己射は、全整数 π で恒等となり同型である。
方針：元の BF 群の両軸による表示と d1 の同値検出を使う。
規約：自己射そのものが恒等とは主張しない。使われ方：元の両射影を保つ積比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.Binary
local instance axesSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

lemma endomorphism_map_eq_id {X Y : OmegaSpectrum.{u}} (f : obj X Y ⟶ obj X Y)
    (hl : SpectrumHo.hom (inl X Y) ≫ SpectrumHo.hom f = SpectrumHo.hom (inl X Y))
    (hr : SpectrumHo.hom (inr X Y) ≫ SpectrumHo.hom f = SpectrumHo.hom (inr X Y))
    (j : ℤ) : homotopyMap f j = MonoidHom.id _ := by
  have hfl := SpectrumHo.homotopyMap_eq_of_hom_eq (inl X Y ≫ f) (inl X Y)
    ((SpectrumHo.hom_comp _ _).trans hl) j
  have hfr := SpectrumHo.homotopyMap_eq_of_hom_eq (inr X Y ≫ f) (inr X Y)
    ((SpectrumHo.hom_comp _ _).trans hr) j
  ext a
  have h := congrArg (homotopyMap f j) (axes X Y j a)
  rw [map_mul, map_comp_apply (inl X Y) f, map_comp_apply (inr X Y) f, hfl, hfr] at h
  exact h.symm.trans (axes X Y j a)

lemma isIso_of_axes_fixed {X Y : OmegaSpectrum.{u}} (f : SpectrumHo.obj (obj X Y) ⟶
    SpectrumHo.obj (obj X Y))
    (hl : SpectrumHo.hom (inl X Y) ≫ f = SpectrumHo.hom (inl X Y))
    (hr : SpectrumHo.hom (inr X Y) ≫ f = SpectrumHo.hom (inr X Y)) : IsIso f := by
  let r := SpectrumHo.representative f
  have hlr : SpectrumHo.hom (inl X Y) ≫ SpectrumHo.hom r = SpectrumHo.hom (inl X Y) := by
    rw [SpectrumHo.hom_representative]
    exact hl
  have hrr : SpectrumHo.hom (inr X Y) ≫ SpectrumHo.hom r = SpectrumHo.hom (inr X Y) := by
    rw [SpectrumHo.hom_representative]
    exact hr
  have hp : PiIsomorphism r := by
    intro j
    rw [endomorphism_map_eq_id r hlr hrr j]
    exact Function.bijective_id
  have hi : IsIso (SpectrumHo.hom r) := isInvertible_of_piIsomorphism r hp
  simpa only [r, SpectrumHo.hom_representative] using hi

end SerrePositivity.KST.LocalizingInvariants.Binary
