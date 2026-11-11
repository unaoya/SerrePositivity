module

public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramFiberGroupNaturality
public import SerrePositivity.KST.LocalizingInvariants.FunctorHomEvaluateArrowIdentity

/-!
概要：接続射の base 群同型が、元の図式比較の base 頂点の射に自然であることを示す。
方針：右辺固定の正規化を頂点で評価し、base 同型を元の頂点の復号輸送と同定する。
規約：接続射と同じ baseGroupIso を使う。使われ方：接続射の一般自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FiberDiagram

local instance baseGroupNaturalityCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

local instance baseGroupNaturalityNerve : Quasicategory (SimplicialNerve OmegaSpectrum.{u}) :=
  sp_quasicategory

lemma normalization_base_arrow (D : FiberDiagram.{u}) :
    Arrow.mk ((vertex 1 1).map (normalization D).hom) =
      Arrow.mk (𝟙 ((vertex 1 1).obj D)) := by
  have he := functorHomEvaluate_arrow_identity
    (homPre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge (normalization D).hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ D.triangle.square) (stdSimplex.obj₀Equiv.symm 1)
    (normalization_right_arrow D)
  rw [homPre, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_precomp] at he
  rw [vertex_map_evaluate]
  exact he

def baseIso (D : FiberDiagram.{u}) : (vertex 1 1).obj D ≅
    SpectrumHo.obj (SpectrumHo.spectrum ((vertex 1 1).obj D)) :=
  FiberPi.baseIso (NativeFiber.rightMap D.triangle)
  (NativeFiber.asFiberSquare D.triangle D.isFiber)

lemma baseIso_hom_canonical (D : FiberDiagram.{u}) :
    (baseIso D).hom = (SpectrumHo.spectrumIso ((vertex 1 1).obj D)).inv := by
  have ha : Arrow.mk (baseIso D).hom = Arrow.mk (𝟙 ((vertex 1 1).obj D)) := by
    unfold baseIso
    rw [← normalization_base]
    exact (arrow_mk_comp_eqToHom ((vertex 1 1).map (normalization D).hom)
      (congrArg HomotopyCategory.mk (FiberModel.homotopyFiberSquare_target_vertex
        (NativeFiber.rightMap D.triangle)))).trans (normalization_base_arrow D)
  simp only [SpectrumHo.spectrumIso, eqToIso.inv]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.hom_eq_eqToHom_of_arrow_identity _ _ ha

def baseGroupIso (D : FiberDiagram.{u}) (j : ℤ) :
    (SpectrumHo.piFunctor j).obj ((vertex 1 1).obj D) ≅
      CommGrpCat.of (homotopyGroup (SpectrumHo.spectrum ((vertex 1 1).obj D)) j) :=
  FiberPi.baseGroupIso (NativeFiber.rightMap D.triangle)
    (NativeFiber.asFiberSquare D.triangle D.isFiber) j

lemma baseGroupIso_naturality {D E : FiberDiagram.{u}} (f : D ⟶ E) (j : ℤ) :
    (SpectrumHo.piFunctor j).map ((vertex 1 1).map f) ≫ (baseGroupIso E j).hom =
      (baseGroupIso D j).hom ≫ CommGrpCat.ofHom (homotopyMap (comparisonMap f 1 1) j) := by
  apply FiberPi.group_naturality
  change (baseIso D).hom ≫ SpectrumHo.hom (comparisonMap f 1 1) =
    (vertex 1 1).map f ≫ (baseIso E).hom
  rw [baseIso_hom_canonical, baseIso_hom_canonical, comparisonMap_hom]
  simp only [SpectrumHo.normalize, Iso.inv_hom_id_assoc]

end SerrePositivity.KST.LocalizingInvariants.FiberDiagram
