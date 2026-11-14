module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedCoherentProductNativeLegs
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.TotalKanMapCocone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.CoherentTransformationUnitCocone

/-!
概要：native 積の両 Kan 脚の単位表現を、元の射影変換と単位の合成余錐へ比較する。
方針：同じ脚の Kan ホモトピーを余錐空間へ反映し、指定合成三角形の比較を続ける。
規約：余錐全体と元の三角形を保持。使われ方：sifted 余極限の積比較の余錐側の界面。

対応節は Kerodon 9.7（Tag 06ZD）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories
variable {B : SSet.{u}} [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B]
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})

/-- 元の native 積の第一 Kan 脚の単位表現を実現した、積図式上の余錐。 -/
def siftedCoherentProductLeftLegCocone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct F G) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanMapCocone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct F G) F
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedCoherentProductNativeKanLeg F G ⟨⟨true⟩⟩)

/-- 第一脚の単位表現の余錐は、第一図式の元の余極限頂点を持つ。 -/
lemma siftedCoherentProductLeftLegCocone_vertex :
    (siftedCoherentProductLeftLegCocone F G).vertex = _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex F :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanMapCocone_vertex _ _ _

/-- 第一脚の単位表現の全余錐は、元の射影変換と単位の任意の指定合成三角形の余錐と同型。 -/
def siftedCoherentProductLeftLegCoconeIso
    (T : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTransformationUnitTriangle (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct F G) F
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductFstVertex F G)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct F G)
      (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex F))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt (siftedCoherentProductLeftLegCocone F G)
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex F) (siftedCoherentProductLeftLegCocone_vertex F G))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationUnitCocone
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct F G) F (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductFstVertex F G) T)
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex F) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationUnitCocone_vertex _ _ _ T)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanMapCoconeIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct F G) F
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductTotalFst F G)
    (Classical.choice (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedCoherentProductNativeKanLeg_left F G)) ≪≫
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationUnitCoconeIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct F G) F
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductFstVertex F G) T).symm

/-- 元の native 積の第二 Kan 脚の単位表現を実現した、積図式上の余錐。 -/
def siftedCoherentProductRightLegCocone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct F G) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanMapCocone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct F G) G
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedCoherentProductNativeKanLeg F G ⟨⟨false⟩⟩)

/-- 第二脚の単位表現の余錐は、第二図式の元の余極限頂点を持つ。 -/
lemma siftedCoherentProductRightLegCocone_vertex :
    (siftedCoherentProductRightLegCocone F G).vertex = _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanMapCocone_vertex _ _ _

/-- 第二脚の単位表現の全余錐も、元の射影変換と単位の任意の指定合成三角形の余錐と同型。 -/
def siftedCoherentProductRightLegCoconeIso
    (T : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTransformationUnitTriangle (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct F G) G
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductSndVertex F G)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct F G)
      (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt (siftedCoherentProductRightLegCocone F G)
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G) (siftedCoherentProductRightLegCocone_vertex F G))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationUnitCocone
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct F G) G (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductSndVertex F G) T)
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationUnitCocone_vertex _ _ _ T)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanMapCoconeIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct F G) G
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductTotalSnd F G)
    (Classical.choice (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedCoherentProductNativeKanLeg_right F G)) ≪≫
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationUnitCoconeIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct F G) G
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductSndVertex F G) T).symm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories
