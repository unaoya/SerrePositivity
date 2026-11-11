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
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FiberModel

local instance replacedComparisonSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

local instance replacedComparisonNerveQuasicategory :
    Quasicategory (SimplicialNerve OmegaSpectrum.{u}) := sp_quasicategory

variable {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y)
  [hp : ∀ n, Fibration (p.app n).right]

def replacedConeEdge := SSet.Edge.ofTruncated
  (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram p (fromPoint Y))))
  (replacedConeComparison p)

lemma replacedConeEdge_isInvertible : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
    (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram p (fromPoint Y))))
    (replacedConeEdge p).toTruncated := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.derived_rightFibration_reflects_invertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _)
    (replacedConeComparison p)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (replacedConeComparison_projection p)).mpr
    (comparison_isInvertible p hp)

def replacedConeDiagramIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (Y := Sp.{u}) (replacedCone p).val (infinityCone p).val :=
  SliceConeComparison.iso (X := Sp.{u}) (replacedConeEdge p) (replacedConeEdge_isInvertible p)

lemma replacedConeDiagramIso_base :
    Arrow.mk (homPre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] _) (replacedConeDiagramIso p).hom) =
      Arrow.mk (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram p (fromPoint Y)))))) :=
  SliceConeComparison.base_arrow (replacedConeEdge p)

lemma replacedConeDiagramIso_apex :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (X := Sp.{u})
      (replacedConeDiagramIso p).hom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinApexVertex _)) =
      Arrow.mk (SpectrumHo.hom (comparison p hp)) := by
  change Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (X := Sp.{u})
    (SliceConeComparison.hom (X := Sp.{u}) (replacedConeEdge p))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinApexVertex _)) = _
  rw [SliceConeComparison.apex_arrow (X := Sp.{u})]
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  exact replacedConeComparison_projection p

end SerrePositivity.KST.LocalizingInvariants.FiberModel
