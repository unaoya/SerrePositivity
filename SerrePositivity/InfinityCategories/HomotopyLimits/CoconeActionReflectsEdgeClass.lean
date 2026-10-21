module

public import SerrePositivity.InfinityCategories.HomotopyLimits.NativeTotalUnitHomClass

/-!
概要：元の指定余極限余錐の全作用の同型から、同じ元の頂点辺の Hom 類を反映する。
方針：全 Hom の余極限同値の充満忠実性と、左模型から区間模型の頂点式を使う。
規約：指定余錐・元の両辺・全余錐作用を保持する。
使われ方：実際の前層余極限脚を元の全空間 Kan 脚と同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open SSet.Truncated.HomotopyCategory

/-- 元の余極限余錐に対する全作用が同型なら、元の両頂点辺は同じ Hom 類。 -/
lemma coconeAction_reflects_edge_homMk {K X : SSet.{u}} [Quasicategory X]
    {F : K ⟶ X} (c : JoinCocone F) (hc : IsColimitCone c) {y : X _⦋0⦌}
    (e f : SSet.Edge c.vertex y)
    (h : VertexIso (X := coconeMappingSpace F y)
      ((coconePointHomFamily c y).app (Opposite.op ⦋0⦌) (leftHomEdgePoint e))
      ((coconePointHomFamily c y).app (Opposite.op ⦋0⦌) (leftHomEdgePoint f))) :
    homMk e.toTruncated = homMk f.toTruncated := by
  have H := (coconePointHomFamily_homotopyEquivalence c hc y).isQCatEquivalence.isFullyFaithful
  let i : VertexIso (X := pinchedHomLeft c.vertex y) (leftHomEdgePoint e) (leftHomEdgePoint f) :=
    H.preimageVertexIso h
  have j := VertexIso.map i (pinchedHomLeftToIntervalMappingSpace c.vertex y)
  rw [leftHomEdgePoint_interval, leftHomEdgePoint_interval] at j
  have he : intervalMappingEdgeOfVertex (intervalMappingVertexOfEdge e) = e :=
    (intervalMappingEdgeVertexEquiv _ _).symm_apply_apply e
  have hf : intervalMappingEdgeOfVertex (intervalMappingVertexOfEdge f) = f :=
    (intervalMappingEdgeVertexEquiv _ _).symm_apply_apply f
  simpa only [he, hf] using intervalRecoveredHom_eq_of_vertexIso j

/-- 同じ Kan 辺の全余錐作用と指定辺の全作用の比較から、元の同じ二辺の類を回収。 -/
lemma totalKanNativeEdge_homMk_of_coconeIso {B C : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ SpaceInfinity.{u})
    (a : F2.coherentDiagramTotalKan F ⟶ F2.coherentDiagramTotalKan G)
    (e : SSet.Edge (F2.coherentDiagramTotalCocone F).vertex (F2.coherentDiagramTotalVertex G))
    (h : VertexIso (X := coconeMappingSpace F (F2.coherentDiagramTotalVertex G))
      ((coconePointHomFamily (F2.coherentDiagramTotalCocone F)
        (F2.coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌) (totalKanNativeHomPoint F G a))
      ((coconePointHomFamily (F2.coherentDiagramTotalCocone F)
        (F2.coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌) (leftHomEdgePoint e))) :
    homMk (totalKanNativeEdge F G a).toTruncated = homMk e.toTruncated :=
  coconeAction_reflects_edge_homMk (F2.coherentDiagramTotalCocone F)
    (F2.coherentDiagramTotalCocone_isColimit F) (totalKanNativeEdge F G a) e h

end SerrePositivity.InfinityCategories.HomotopyLimits
