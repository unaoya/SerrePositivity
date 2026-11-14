module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.IntervalIsoHomClass
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.KanNativeCoconeUnitCriterion

/-!
概要：標準 native 余錐の元の変換を、選択済み全空間単位の同じ Hom 類へ照合する。
方針：元の全空間余錐の実現比較を区間同型へ移し、同じ回収辺の類を反映する。
規約：元の標準余錐・単位表現・Kan 辺の作用を保持する。
使われ方：実際の脚の標準単位正方形から全余錐作用への比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SSet.Truncated.HomotopyCategory
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})

/-- 元の全空間余錐の標準変換は、選択済みの同じ単位表現と区間内で同型。 -/
def nativeTotalUnitTransformationIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeTransformationPointAt (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F)
      (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone_vertex F)) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalUnitRepresentation F).1 :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.realizedCoconeTransformationIso (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalUnitRepresentation F).1
    (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentTotalCoconeRealization F)

/-- 元の標準 native 余錐変換と選択済み単位から回収した辺は、同じ Hom 類。 -/
lemma nativeTotalUnitTransformation_homMk :
    homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeTransformationPointAt
      (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F) (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone_vertex F))).toTruncated =
    homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalUnitRepresentation F).1).toTruncated :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.intervalRecoveredHom_eq_of_vertexIso (nativeTotalUnitTransformationIso F)

/-- 元の native 標準単位との合成類から、同じ Kan 辺と指定余錐の全作用を比較。 -/
def kanNativeCoconeIsoOfNativeUnitHomClass
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G) _⦋0⦌)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) (hz : c.vertex = _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)
    (h : homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex t).toTruncated ≫
      homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeTransformationPointAt
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone G) (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone_vertex G))).toTruncated =
      homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeTransformationPointAt c hz)).toTruncated) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F)
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanNativeHomPoint F G (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransformationTotalKanMap F G t)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt c (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G) hz) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanNativeCoconeIsoOfUnitHomClass F G t c hz
  rw [nativeTotalUnitTransformation_homMk G] at h
  exact h

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
