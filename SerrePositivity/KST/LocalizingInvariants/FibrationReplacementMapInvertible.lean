module

public import SerrePositivity.KST.LocalizingInvariants.FibrationReplacementUnitPath
public import SerrePositivity.KST.LocalizingInvariants.SpectrumComponentClass
public import SerrePositivity.KST.Spectra.SpectrumIntegerHomotopyDetection

/-!
概要：源の BF 射が全整数 π 同型なら、指定された fibration 置換比較も可逆になる。
方針：元の単位の相対区間で二合成の h Sp の類を等置し、可逆単位を相殺する。
規約：構成した比較射を保持。使われ方：fiber 比較の単位 cube の底図式の可逆性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FibrationReplacementComparison

local instance replacementMapInvertibleCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)

lemma unitPath_hom : SpectrumHo.hom (fibrationReplacementUnit p) ≫ SpectrumHo.hom (map p q a b h) =
    SpectrumHo.hom a ≫ SpectrumHo.hom (fibrationReplacementUnit q) := by
  have he := SpectrumHo.hom_eq_of_component_eq _ _ (π₀.sound (unitPath p q a b h).path)
  simpa only [SpectrumHo.hom_comp] using he

lemma map_isInvertible (ha : PiIsomorphism a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (map p q a b h)).toTruncated := by
  haveI : IsIso (SpectrumHo.hom (fibrationReplacementUnit p)) :=
    isInvertible_of_piIsomorphism _ (fibrationReplacementUnit_piIsomorphism p)
  haveI : IsIso (SpectrumHo.hom (fibrationReplacementUnit q)) :=
    isInvertible_of_piIsomorphism _ (fibrationReplacementUnit_piIsomorphism q)
  haveI : IsIso (SpectrumHo.hom a) := isInvertible_of_piIsomorphism a ha
  haveI : IsIso (SpectrumHo.hom (fibrationReplacementUnit p) ≫
      SpectrumHo.hom (map p q a b h)) := by
    rw [unitPath_hom]
    infer_instance
  exact (isIso_comp_left_iff (SpectrumHo.hom (fibrationReplacementUnit p))
    (SpectrumHo.hom (map p q a b h))).mp inferInstance

end SerrePositivity.KST.LocalizingInvariants.FibrationReplacementComparison
