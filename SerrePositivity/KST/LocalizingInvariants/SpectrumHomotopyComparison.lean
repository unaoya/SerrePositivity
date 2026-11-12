module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumHomotopyFunctor

/-!
概要：Sp の π 関手と元の BF 整数次数群の自然な比較。
方針：頂点の復号の等号を対象比較とし、射の類の等号から自然性を得る。
規約：比較は元の BF 射に対して可換する。使われ方：K-5 の長完全列の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumHo

local instance homotopyComparisonSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

lemma hom_eqToHom {X Y : OmegaSpectrum.{u}} (h : X = Y) :
    hom (eqToHom h) = eqToHom (congrArg obj h) := by
  subst Y
  exact hom_id X

/-- 元の BF 対象の頂点を復号すると、元の対象へ戻る。 -/
def spectrumIsoBF (X : OmegaSpectrum.{u}) : spectrum (obj X) ≅ X :=
  eqToIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject_vertex X)

lemma spectrumIsoBF_hom (X : OmegaSpectrum.{u}) :
    hom (spectrumIsoBF X).hom = (spectrumIso (obj X)).hom :=
  hom_eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject_vertex X)

/-- 全整数次数で、元の BF 射とホモトピー圏の作用の比較は可換する。 -/
lemma piMap_hom_naturality {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (j : ℤ) :
    (homotopyMap (spectrumIsoBF Y).hom j).comp (piMap (hom f) j) =
      (homotopyMap f j).comp (homotopyMap (spectrumIsoBF X).hom j) := by
  have h : hom (representative (normalize (hom f)) ≫ (spectrumIsoBF Y).hom) =
      hom ((spectrumIsoBF X).hom ≫ f) := by
    rw [hom_comp, hom_comp, hom_representative, spectrumIsoBF_hom, spectrumIsoBF_hom]
    simp only [normalize, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (homotopyMap_comp _ _ j).symm.trans
    ((homotopyMap_eq_of_hom_eq _ _ h j).trans (homotopyMap_comp _ _ j))

/-- Sp の π 関手の値を元の BF 整数次数群に同定する。 -/
def piComparison (X : OmegaSpectrum.{u}) (j : ℤ) :
    (piFunctor j).obj (obj X) ≅ CommGrpCat.of (homotopyGroup X j) :=
  (homotopyFunctor j).mapIso (spectrumIsoBF X)

lemma piComparison_naturality {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (j : ℤ) :
    (piFunctor j).map (hom f) ≫ (piComparison Y j).hom =
      (piComparison X j).hom ≫ CommGrpCat.ofHom (homotopyMap f j) :=
  congrArg CommGrpCat.ofHom (piMap_hom_naturality f j)

end SerrePositivity.KST.LocalizingInvariants.SpectrumHo
