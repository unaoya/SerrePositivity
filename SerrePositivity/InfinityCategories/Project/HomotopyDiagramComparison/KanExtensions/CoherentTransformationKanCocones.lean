module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.CoherentInvertibleTotalKan
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.CoherentTransformationUnitCocone

/-!
概要：元の coherent 変換の Kan 像による全余錐作用を、指定単位三角形へ照合する。
方針：元の Kan 射の単位表示・元の全空間写像余錐・同じ合成三角形の比較を続ける。
規約：元の辺・変換・全余錐・指定三角形を保持。可逆性や底の充填性は不要。
使われ方：P_Σ の元の全錐比較を、余極限の全脚へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (T : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTransformationUnitTriangle F G t)

/-- 元の同じ Kan 像の単位表現の余錐は、指定単位三角形の元の余錐に同型。 -/
def coherentTransformationKanUnitCoconeIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanMapCocone F G (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransformationTotalKanMap F G t))
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanMapCocone_vertex _ _ _))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationUnitCocone F G t T)
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationUnitCocone_vertex F G t T)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanMapCoconeIso F G (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap F G t)
    (SSet.RelativeMorphism.Homotopy.refl _) ≪≫
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationUnitCoconeIso F G t T).symm

/-- 元の同じ Kan 比較辺の全余錐作用は、元の変換と指定単位の全三角形へ移る。 -/
def coherentTransformationKanNativeUnitCoconeIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F)
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanNativeHomPoint F G (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransformationTotalKanMap F G t)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationUnitCocone F G t T)
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationUnitCocone_vertex F G t T)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransformationTotalKanNativeCoconeIso F G t ≪≫
    coherentTransformationKanUnitCoconeIso F G t T

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
