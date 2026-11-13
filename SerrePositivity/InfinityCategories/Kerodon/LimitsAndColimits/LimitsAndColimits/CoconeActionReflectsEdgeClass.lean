module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.UnitComparisons.NativeTotalUnitHomClass

/-!
概要：元の指定余極限余錐の全作用の同型から、同じ元の頂点辺の Hom 類を反映する。
方針：全 Hom の余極限同値の充満忠実性と、左模型から区間模型の頂点式を使う。
規約：指定余錐・元の両辺・全余錐作用を保持する。
使われ方：実際の前層余極限脚を元の全空間 Kan 脚と同定する。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SSet.Truncated.HomotopyCategory

/-- 元の余極限余錐に対する全作用が同型なら、元の両頂点辺は同じ Hom 類。 -/
lemma coconeAction_reflects_edge_homMk {K X : SSet.{u}} [Quasicategory X]
    {F : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) {y : X _⦋0⦌}
    (e f : SSet.Edge c.vertex y)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily c y).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftHomEdgePoint e))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily c y).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftHomEdgePoint f))) :
    homMk e.toTruncated = homMk f.toTruncated := by
  have H := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily_homotopyEquivalence c hc y).isQCatEquivalence.isFullyFaithful
  let i : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft c.vertex y) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftHomEdgePoint e) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftHomEdgePoint f) :=
    H.preimageVertexIso h
  have j := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftToIntervalMappingSpace c.vertex y)
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftHomEdgePoint_interval, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftHomEdgePoint_interval] at j
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge e) = e :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeVertexEquiv _ _).symm_apply_apply e
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge f) = f :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeVertexEquiv _ _).symm_apply_apply f
  simpa only [he, hf] using _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.intervalRecoveredHom_eq_of_vertexIso j

/-- 同じ Kan 辺の全余錐作用と指定辺の全作用の比較から、元の同じ二辺の類を回収。 -/
lemma totalKanNativeEdge_homMk_of_coconeIso {B C : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (a : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan F ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan G)
    (e : SSet.Edge (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F).vertex (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G))
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F)
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanNativeHomPoint F G a))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F)
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftHomEdgePoint e))) :
    homMk (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanNativeEdge F G a).toTruncated = homMk e.toTruncated :=
  coconeAction_reflects_edge_homMk (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramTotalCocone_isColimit F) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanNativeEdge F G a) e h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
