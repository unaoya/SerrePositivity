module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingSpace
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingVertexEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PreFiberKan
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningTransformationFamily
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeRealizationTransformation
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeTransformationMap
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeTransformationPoint
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoherentCoconeTotalComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoherentSmallConstantTarget
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.HomotopyCoconeRealization
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.YonedaHomotopyVertex
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTotalCocone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTotalObject
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTotalUnitRepresentation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeMappingSpace

/-!
概要：構成した native 全空間余錐の標準比較の像を元の実際の単位と比較する。
方針：実現の比較を変換空間へ戻し、元の単位の表現同型と合成する。
規約：指定図式・余錐・頂点・単位を保持する。
使われ方：全 Hom の余極限判定で使う単位の追跡。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {B : SSet.{u}}

/-- 概要：native 全空間余錐の比較の像は元の全空間の単位と同型。
方針：両端固定の実現比較を写し、元の単位を表す選択済みの同型と続ける。
規約：全空間の実際の単位。使われ方：余錐の全 Hom 普遍性の単位整合。 -/
def coherentTotalCoconeUnitIso
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := (SSet.uliftFunctor.{u + 1, u}).obj
      ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F)).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalVertex F)).obj))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coherentCoconeTotalComparison F (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalVertex F)).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone F) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalVertex F)
          (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone_vertex F)))
      (ULift.up.{u + 1, u} (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalUnit F))) := by
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeRealizationTransformationHomotopy
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalUnitRepresentation F).1 (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalCoconeRealization F)
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.vertexIsoOfYonedaHomotopy H
  exact e.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coherentSmallConstantTargetMap F (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalVertex F)) ≪≫
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalUnitRepresentation F).2

end SerrePositivity.InfinityCategories.Project.FilteredExchange
