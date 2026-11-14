module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.RealizedCoconeComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CoherentDiagrams.CoherentTriangleFromHomClass
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.CoherentTransformationKanCocones

/-!
概要：元の変換と指定単位の合成を表す指定余錐を、同じ Kan 辺の全余錐作用へ照合する。
方針：同じ長辺の単位三角形と実現比較を用い、全余錐空間の充満忠実性で反映する。
規約：元の図式・変換・Kan 像・指定余錐を保持する。底の quasicategory 性は不要。
使われ方：実際の前層余極限脚を標準全評価 Kan 脚と比較する。
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
  (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) (hz : c.vertex = _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)

/-- 同じ単位三角形の長辺を表す指定余錐は、同じ Kan 辺の全余錐作用と同型。 -/
def kanNativeCoconeIsoOfUnitTriangle
    (T : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTransformationUnitTriangle F G t)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeTransformationPointAt c hz) T.diagonal) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F)
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanNativeHomPoint F G (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransformationTotalKanMap F G t)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt c (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G) hz) := by
  let R := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentRepresentationCoconeRealization F (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap F G t ≫ _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalUnit G)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationUnitRepresentation F G t T)
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransformationKanNativeUnitCoconeIso F G t T ≪≫
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeRealizationComparisonIso T.diagonal R c hz e).symm

/-- 指定余錐の変換が元の変換と指定単位の合成類なら、同じ Kan 辺の作用と同型。 -/
def kanNativeCoconeIsoOfUnitHomClass
    (h : homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex t).toTruncated ≫
      homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalUnitRepresentation G).1).toTruncated =
        homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeTransformationPointAt c hz)).toTruncated) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F)
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanNativeHomPoint F G (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransformationTotalKanMap F G t)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt c (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G) hz) :=
  kanNativeCoconeIsoOfUnitTriangle F G t c hz
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransformationTriangleOfHomClass t (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalUnitRepresentation G).1
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeTransformationPointAt c hz) h) (Iso.refl _)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
