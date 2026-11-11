module

public import SerrePositivity.KST.LocalizingInvariants.FibrationReplacementUnitPath
public import SerrePositivity.KST.LocalizingInvariants.SpectrumMappingIntervalConstant

/-!
概要：fibration 置換単位の相対区間を、端点を固定した Sp の辺の全族と同型へ移す。
方針：指定 BF 区間に標準の coherent 区間比較を適用し、射影した区間の恒等性も保持する。
規約：指定 prism との全関手比較の照合は別工程。使われ方：右辺 prism の二次比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FibrationReplacementComparison

local instance unitIntervalCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)

def unitHomotopy := SpectrumMappingPath.homotopy (unitPath p q a b h).path

def unitArrowIso := SpectrumMappingPath.arrowIso (unitPath p q a b h).path

lemma unitHomotopy_source :
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 1})) ≫ (unitHomotopy p q a b h).h =
      fst (Δ[0] : SSet.{u + 1}) Δ[1] ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) :=
  SpectrumMappingPath.homotopy_source _

lemma unitHomotopy_target :
    (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 1})) ≫ (unitHomotopy p q a b h).h =
      fst (Δ[0] : SSet.{u + 1}) Δ[1] ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (fibrationReplacement q)) :=
  SpectrumMappingPath.homotopy_target _

lemma unitFirst_projection : (fibrationReplacementUnit p ≫ map p q a b h) ≫
    fibrationReplacementProjection q = p ≫ b := by
  rw [Category.assoc, map_projection, ← Category.assoc, fibrationReplacement_fac]

include h in
lemma unitSecond_projection : (a ≫ fibrationReplacementUnit q) ≫
    fibrationReplacementProjection q = p ≫ b := by
  rw [Category.assoc, fibrationReplacement_fac, h]

def unitProjectedEdge : (mappingSpace X Y').Edge (vertexOfHom (p ≫ b))
    (vertexOfHom (p ≫ b)) :=
  ((unitPath p q a b h).path.map
    (SpectrumMappingAcyclic.post X (fibrationReplacementProjection q))).ofEq
      ((SpectrumMappingAcyclic.post_vertex _ _).trans
        (congrArg vertexOfHom (unitFirst_projection p q a b h)))
      ((SpectrumMappingAcyclic.post_vertex _ _).trans
        (congrArg vertexOfHom (unitSecond_projection p q a b h)))

lemma unitProjectedEdge_id : unitProjectedEdge p q a b h =
    SSet.Edge.id (vertexOfHom (p ≫ b)) := by
  apply SSet.Edge.ext
  exact (unitPath_over_projection p q a b h).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _)

lemma unitProjectedArrowEdge_id : SpectrumMappingPath.arrowEdge
    (unitProjectedEdge p q a b h) =
      SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (p ≫ b)).edge)) := by
  rw [unitProjectedEdge_id, SpectrumMappingPath.arrowEdge_id]

end SerrePositivity.KST.LocalizingInvariants.FibrationReplacementComparison
