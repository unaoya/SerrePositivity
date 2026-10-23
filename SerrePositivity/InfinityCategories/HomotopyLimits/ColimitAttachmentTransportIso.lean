module

public import SerrePositivity.InfinityCategories.HomotopyLimits.LiftedEdgeTransportPointIso
public import SerrePositivity.InfinityCategories.HomotopyLimits.ColimitAttachmentTransport
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationTransportNaturality
public import SerrePositivity.InfinityCategories.HomotopyLimits.TransportedCoconeGluing
public import SerrePositivity.InfinityCategories.F1B.KanFunctorHomotopyClasses

/-!
概要：付加比較辺の終点と、その辺に沿う共通余錐の輸送を指定同型で結ぶ。
方針：実際の余錐圏の比較辺と底上の制限の輸送自然性を使う。
規約：連結成分だけでなく指定した点図式間の同型。使われ方：span の三角形から境界経路への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A C X : SSet.{u}} [Quasicategory X] {p : A ⟶ X}
  (c : JoinCocone p) (hc : IsColimitCone c) (i : A ⟶ C)
  (F : C ⟶ X) (hi : i ≫ F = p) (d : JoinCocone F)

/-- 元の部分余錐の境界は、実際の付加比較辺に沿う共通余錐の輸送像と指定同型で結ばれる。 -/
def colimitAttachmentTransportPointIso :
    FunctorIso (SSet.yonedaEquiv.symm (colimitAttachmentFiberVertex i F hi d))
      (SSet.yonedaEquiv.symm (initialFiberVertexAt (sliceUnderProjection p) c c.vertex rfl) ≫
        edgeTransport (sliceUnderProjection p) (colimitAttachmentApexEdge c hc i F hi d)) := by
  apply liftedEdgeTransportPointIso (sliceUnderProjection p)
    (SSet.Edge.ofTruncated (colimitAttachmentApexEdge c hc i F hi d))
    (initialFiberVertexAt (sliceUnderProjection p) c c.vertex rfl)
    (colimitAttachmentFiberVertex i F hi d) (colimitAttachmentCoconeEdge c hc i F hi d)
  exact (coconeComparisonEdge_projection c (colimitAttachmentComparison c hc i F hi d)).trans
    (colimitAttachmentComparison_leg_edge c hc i F hi d)

/-- 部分余錐を輸送してから境界へ制限した点は、元の境界を同じ辺で輸送した点と指定同型で結ばれる。 -/
def coconeBoundaryTransportPointIso {y : X _⦋0⦌} (e : X.Edge d.vertex y) :
    FunctorIso
      (SSet.yonedaEquiv.symm (transportedCoconeVertex d e) ≫
        normalizedCoconeRestrictionFiber F i hi y)
      (SSet.yonedaEquiv.symm (colimitAttachmentFiberVertex i F hi d) ≫
        edgeTransport (sliceUnderProjection p) e) := by
  let v := initialFiberVertexAt (sliceUnderProjection F) d d.vertex rfl
  have hb : SSet.yonedaEquiv.symm v ≫ normalizedCoconeRestrictionFiber F i hi d.vertex =
      SSet.yonedaEquiv.symm (colimitAttachmentFiberVertex i F hi d) := by
    rw [SSet.yonedaEquiv_symm_comp]
    exact congrArg SSet.yonedaEquiv.symm (normalizedCoconeRestrictionFiber_vertex F i hi d)
  have ht : SSet.yonedaEquiv.symm (transportedCoconeVertex d e) =
      SSet.yonedaEquiv.symm v ≫ edgeTransport (sliceUnderProjection F) e :=
    (SSet.yonedaEquiv_symm_comp v (edgeTransport (sliceUnderProjection F) e)).symm
  have I := FunctorIso.precomp
    (leftFibrationMap_transportIso (sliceUnderProjection F) (sliceUnderProjection p)
      (normalizedCoconeRestriction F i hi) (normalizedCoconeRestriction_projection F i hi) e)
    (SSet.yonedaEquiv.symm v)
  change FunctorIso
    (SSet.yonedaEquiv.symm v ≫ (edgeTransport (sliceUnderProjection F) e ≫
      normalizedCoconeRestrictionFiber F i hi y))
    (SSet.yonedaEquiv.symm v ≫ (normalizedCoconeRestrictionFiber F i hi d.vertex ≫
      edgeTransport (sliceUnderProjection p) e)) at I
  exact kanFunctorIsoTransport I
    ((Category.assoc _ _ _).symm.trans (congrArg
      (fun z ↦ z ≫ normalizedCoconeRestrictionFiber F i hi y) ht.symm))
    ((Category.assoc _ _ _).symm.trans (congrArg
      (fun z ↦ z ≫ edgeTransport (sliceUnderProjection p) e) hb))

end
end SerrePositivity.InfinityCategories.HomotopyLimits
