module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.LiftedEdgeTransportCylinder
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitAttachmentTransportIso

/-!
概要：指定境界経路の付加比較同型を、同じ実際の付加辺の相対円柱として保持する。
方針：付加比較辺自身の一点 prism を標準輸送と比較し、既存の同型の類を照合する。
規約：付加辺・底の辺・元の共通余錐を保持する。使われ方：指定経路の長辺延長への接続。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {A C X : SSet.{u}} [Quasicategory X] {p : A ⟶ X}
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (i : A ⟶ C)
  (F : C ⟶ X) (hi : i ≫ F = p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p
local notation "e" => SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentApexEdge c hc i F hi d)
local notation "v" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialFiberVertexAt q c (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex c) rfl
local notation "w" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentFiberVertex i F hi d
local notation "k" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentCoconeEdge c hc i F hi d

omit [Quasicategory X] in
/-- 実際の付加比較辺を被覆する底の辺は、元の付加頂点比較辺。 -/
lemma colimitAttachmentTransportCylinder_edge_projection : ((k).map q).edge = (e).edge :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeComparisonEdge_projection c (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentComparison c hc i F hi d)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentComparison_leg_edge c hc i F hi d)

/-- 付加比較辺と同じ標準輸送を、底・初期値固定の円柱で結ぶ実際のデータ。 -/
def colimitAttachmentTransportCylinderData :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedEdgeTransportCylinderData q e v w k
    (colimitAttachmentTransportCylinder_edge_projection c hc i F hi d)

/-- 付加比較同型を表す、元の付加辺の同じ相対円柱から得る終点比較。 -/
def colimitAttachmentTransportHomotopy : SSet.Homotopy (SSet.yonedaEquiv.symm w)
    (SSet.yonedaEquiv.symm v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentApexEdge c hc i F hi d)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedEdgeTransportEndpointHomotopy q e v w k
    (colimitAttachmentTransportCylinder_edge_projection c hc i F hi d)

/-- 付加辺の終点比較の raw な射は、元の底・初期値固定円柱の終点制限そのもの。 -/
lemma colimitAttachmentTransportHomotopy_projection :
    (colimitAttachmentTransportHomotopy c hc i F hi d).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q d.vertex =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[0] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
        (colimitAttachmentTransportCylinderData c hc i F hi d).homotopy.h :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedEdgeTransportEndpointHomotopy_projection q e v w k
    (colimitAttachmentTransportCylinder_edge_projection c hc i F hi d)

/-- 終点円柱の辺の類は、元の指定境界経路が使う付加比較同型の射そのもの。 -/
lemma colimitAttachmentTransportHomotopy_hom :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (colimitAttachmentTransportHomotopy c hc i F hi d)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentTransportPointIso c hc i F hi d).hom :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedEdgeTransportEndpointHomotopy_hom q e v w k
    (colimitAttachmentTransportCylinder_edge_projection c hc i F hi d)

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
