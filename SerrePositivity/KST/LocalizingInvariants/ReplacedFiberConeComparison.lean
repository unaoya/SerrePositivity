module

public import SerrePositivity.KST.LocalizingInvariants.SliceConeComparison
public import SerrePositivity.KST.LocalizingInvariants.BFFiberInfinityCone
public import SerrePositivity.KST.LocalizingInvariants.SpectrumHomClass

/-!
概要：置換済み BF fiber の錐と実 fiber の錐の比較を、元の全図式の同型として保持する。
方針：保存済みの slice の辺を全錐の族へ写し、元の比較射の一単体を頂点で回収する。
規約：底は恒等、頂点は元の comparison。使われ方：厳密な fiber cube の置換後への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FiberModel

local instance replacedComparisonSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

local instance replacedComparisonNerveQuasicategory :
    Quasicategory (SimplicialNerve OmegaSpectrum.{u}) := sp_quasicategory

variable {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y)
  [hp : ∀ n, Fibration (p.app n).right]

def replacedConeEdge := SSet.Edge.ofTruncated
  (X := sliceOver (strictCoherentDiagram (spectrumPullbackDiagram p (fromPoint Y))))
  (replacedConeComparison p)

lemma replacedConeEdge_isInvertible : IsInvertibleEdge
    (X := sliceOver (strictCoherentDiagram (spectrumPullbackDiagram p (fromPoint Y))))
    (replacedConeEdge p).toTruncated := by
  apply derived_rightFibration_reflects_invertibleEdge (sliceOverProjection _)
    (replacedConeComparison p)
  exact (isInvertibleEdge_congr (replacedConeComparison_projection p)).mpr
    (comparison_isInvertible p hp)

def replacedConeDiagramIso :
    FunctorIso (Y := Sp.{u}) (replacedCone p).val (infinityCone p).val :=
  SliceConeComparison.iso (X := Sp.{u}) (replacedConeEdge p) (replacedConeEdge_isInvertible p)

lemma replacedConeDiagramIso_base :
    Arrow.mk (homPre (joinInr Δ[0] _) (replacedConeDiagramIso p).hom) =
      Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex
        (strictCoherentDiagram (spectrumPullbackDiagram p (fromPoint Y)))))) :=
  SliceConeComparison.base_arrow (replacedConeEdge p)

lemma replacedConeDiagramIso_apex :
    Arrow.mk (functorHomEvaluate (X := Sp.{u})
      (replacedConeDiagramIso p).hom (joinApexVertex _)) =
      Arrow.mk (SpectrumHo.hom (comparison p hp)) := by
  change Arrow.mk (functorHomEvaluate (X := Sp.{u})
    (SliceConeComparison.hom (X := Sp.{u}) (replacedConeEdge p))
    (joinApexVertex _)) = _
  rw [SliceConeComparison.apex_arrow (X := Sp.{u})]
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  exact replacedConeComparison_projection p

end SerrePositivity.KST.LocalizingInvariants.FiberModel
