module

public import SerrePositivity.InfinityCategories.HomotopyLimits.LiftedEdgeTransportCylinder
public import SerrePositivity.InfinityCategories.HomotopyLimits.ColimitAttachmentTransportIso

/-!
概要：指定境界経路の付加比較同型を、同じ実際の付加辺の相対円柱として保持する。
方針：付加比較辺自身の一点 prism を標準輸送と比較し、既存の同型の類を照合する。
規約：付加辺・底の辺・元の共通余錐を保持する。使われ方：指定経路の長辺延長への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A C X : SSet.{u}} [Quasicategory X] {p : A ⟶ X}
  (c : JoinCocone p) (hc : IsColimitCone c) (i : A ⟶ C)
  (F : C ⟶ X) (hi : i ≫ F = p) (d : JoinCocone F)
local notation "q" => sliceUnderProjection p
local notation "e" => SSet.Edge.ofTruncated (colimitAttachmentApexEdge c hc i F hi d)
local notation "v" => initialFiberVertexAt q c (JoinCocone.vertex c) rfl
local notation "w" => colimitAttachmentFiberVertex i F hi d
local notation "k" => colimitAttachmentCoconeEdge c hc i F hi d

omit [Quasicategory X] in
/-- 実際の付加比較辺を被覆する底の辺は、元の付加頂点比較辺。 -/
lemma colimitAttachmentTransportCylinder_edge_projection : ((k).map q).edge = (e).edge :=
  (coconeComparisonEdge_projection c (colimitAttachmentComparison c hc i F hi d)).trans
    (colimitAttachmentComparison_leg_edge c hc i F hi d)

/-- 付加比較辺と同じ標準輸送を、底・初期値固定の円柱で結ぶ実際のデータ。 -/
def colimitAttachmentTransportCylinderData :=
  liftedEdgeTransportCylinderData q e v w k
    (colimitAttachmentTransportCylinder_edge_projection c hc i F hi d)

/-- 付加比較同型を表す、元の付加辺の同じ相対円柱から得る終点比較。 -/
def colimitAttachmentTransportHomotopy : SSet.Homotopy (SSet.yonedaEquiv.symm w)
    (SSet.yonedaEquiv.symm v ≫ edgeTransport q (colimitAttachmentApexEdge c hc i F hi d)) :=
  liftedEdgeTransportEndpointHomotopy q e v w k
    (colimitAttachmentTransportCylinder_edge_projection c hc i F hi d)

/-- 付加辺の終点比較の raw な射は、元の底・初期値固定円柱の終点制限そのもの。 -/
lemma colimitAttachmentTransportHomotopy_projection :
    (colimitAttachmentTransportHomotopy c hc i F hi d).h ≫ vertexFiberι q d.vertex =
      (prismEndpoint 1 (Δ[0] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
        (colimitAttachmentTransportCylinderData c hc i F hi d).homotopy.h :=
  liftedEdgeTransportEndpointHomotopy_projection q e v w k
    (colimitAttachmentTransportCylinder_edge_projection c hc i F hi d)

/-- 終点円柱の辺の類は、元の指定境界経路が使う付加比較同型の射そのもの。 -/
lemma colimitAttachmentTransportHomotopy_hom :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (colimitAttachmentTransportHomotopy c hc i F hi d)) =
      (colimitAttachmentTransportPointIso c hc i F hi d).hom :=
  liftedEdgeTransportEndpointHomotopy_hom q e v w k
    (colimitAttachmentTransportCylinder_edge_projection c hc i F hi d)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
