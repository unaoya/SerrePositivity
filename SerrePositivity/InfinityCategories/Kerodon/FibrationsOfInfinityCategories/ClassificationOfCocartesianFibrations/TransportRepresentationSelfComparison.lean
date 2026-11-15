module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NativeNerveStraighteningComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RepresentationComparisonCoherence
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality

/-! 同じ表現空間の比較の自己単位則で、元の全native単位を正規化する。 -/

@[expose] public section
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の指定比較の自己単位・合成・評価の法則。 -/
lemma smallFiberTransportRepresentationVertexIso_self {E B : SSet.{u+1}} (p : E ⟶ B) [LeftFibration p]
    (hp : HasSmallSimplexFibers p) (R : LeftTransportRepresentation p) :
    smallFiberTransportRepresentationVertexIso p hp R R = Iso.refl (HomotopyCategory.mk (transportWitnessVertex R)) := by
  exact smallFiberTransportRepresentationVertexIso_unique p hp R R _ _

/-- 元の指定比較の自己単位・合成・評価の法則。 -/
lemma smallFiberTransportRepresentationDiagramIso_self {E B : SSet.{u+1}} (p : E ⟶ B) [LeftFibration p]
    (hp : HasSmallSimplexFibers p) (R : LeftTransportRepresentation p) :
    smallFiberTransportRepresentationDiagramIso p hp R R = Iso.refl (HomotopyCategory.mk (functorVertex R.diagram)) := by
  unfold smallFiberTransportRepresentationDiagramIso
  rw [smallFiberTransportRepresentationVertexIso_self]
  simp [LeftTransportRepresentation.diagramIso, VertexIso.map]

/-- 元の指定比較の自己単位・合成・評価の法則。 -/
lemma nerveCoherentTransportRepresentationIso_self {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    nerveCoherentTransportRepresentationIso p (nerveLeftTransportRepresentation p) =
      Iso.refl (HomotopyCategory.mk (functorVertex (leftCoherentTransport p))) := by
  unfold nerveCoherentTransportRepresentationIso
  exact smallFiberTransportRepresentationDiagramIso_self _ _ _

/-- 元の指定比較の自己単位・合成・評価の法則。 -/
lemma nerveStraighteningRepresentationIso_self {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    nerveStraighteningRepresentationIso p (nerveLeftTransportRepresentation p) =
      leftStraighteningCoherentMap_oppositeVertexIso p := by
  unfold nerveStraighteningRepresentationIso
  rw [nerveCoherentTransportRepresentationIso_self]
  simp

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

end
