module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeStandardVertexHom
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanNativeEdgeUnitSquare
public import SerrePositivity.InfinityCategories.Stable.CoconeFactorization

/-!
概要：元の全余錐の脚の頂点共役辺は、同じ底変換の標準全空間 Kan 辺と同じ類を持つ。
方針：頂点共役の定値像と元の標準単位正方形を照合し、全余錐作用の判定で反映する。
規約：元の coslice 比較・全余錐脚・全空間 Kan 像を保持。底の充填性は要求しない。
使われ方：実際の前層余極限脚と全評価 Kan 脚の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open SSet.Truncated.HomotopyCategory
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  {q : JoinCocone F} {d : JoinCocone G}
  (i : VertexIso (X := sliceUnder F) q (F2.coherentDiagramTotalCocone F))
  (j : VertexIso (X := sliceUnder G) d (F2.coherentDiagramTotalCocone G))
  (e : SSet.Truncated.Edge
    (X := (truncation 2).obj ((ihom (join ((SSet.uliftFunctor.{u + 1, u}).obj B)
      (Δ[0] : SSet.{u + 1}))).obj SpaceInfinity.{u}))
    (functorVertex q.val) (functorVertex d.val))

/-- 元の頂点共役辺を、同じ標準 Kan 頂点の指定終点で表示する。 -/
def standardCoconeKanLegEdge :
    SSet.Edge (F2.coherentDiagramTotalCocone F).vertex (F2.coherentDiagramTotalVertex G) :=
  (coconeStandardVertexEdge i j e).ofEq rfl (F2.coherentDiagramTotalCocone_vertex G)

/-- 終点表示を揃えた同じ頂点辺の類は、元の共役射の同じ終点輸送。 -/
lemma standardCoconeKanLegEdge_homMk :
    homMk (standardCoconeKanLegEdge F G i j e).toTruncated =
      coconeStandardVertexHom i j e ≫ eqToHom (congrArg HomotopyCategory.mk
        (F2.coherentDiagramTotalCocone_vertex G)) := by
  rw [← coconeStandardVertexEdge_homMk i j e]
  exact (homMk_comp_eqToHom_of_edge_eq (coconeStandardVertexEdge i j e).toTruncated
    (standardCoconeKanLegEdge F G i j e).toTruncated
    (F2.coherentDiagramTotalCocone_vertex G) rfl).symm

/-- 元の頂点共役辺の定値変換は、同じ元の底脚と両標準単位について可換。 -/
lemma standardCoconeKanLeg_unit_square :
    homMk (coconeWholeEdgeBottom q d e).toTruncated ≫
      homMk (intervalMappingEdgeOfVertex (coconeTransformationPointAt
        (F2.coherentDiagramTotalCocone G) (F2.coherentDiagramTotalCocone_vertex G))).toTruncated =
    homMk (intervalMappingEdgeOfVertex
      (F2.coconeTransformationVertex (F2.coherentDiagramTotalCocone F))).toTruncated ≫
      homMk (constantFunctorEdge (A := (SSet.uliftFunctor.{u + 1, u}).obj B)
        (standardCoconeKanLegEdge F G i j e).toTruncated) := by
  exact F2.homMk_square_transport
    (coconeWholeEdgeBottom q d e).toTruncated
    (intervalMappingEdgeOfVertex
      (F2.coconeTransformationVertex (F2.coherentDiagramTotalCocone G))).toTruncated
    (intervalMappingEdgeOfVertex
      (F2.coconeTransformationVertex (F2.coherentDiagramTotalCocone F))).toTruncated
    (constantFunctorEdge (A := (SSet.uliftFunctor.{u + 1, u}).obj B)
      (coconeStandardVertexEdge i j e).toTruncated)
    (coconeWholeEdgeBottom q d e).toTruncated
    (intervalMappingEdgeOfVertex (coconeTransformationPointAt
      (F2.coherentDiagramTotalCocone G) (F2.coherentDiagramTotalCocone_vertex G))).toTruncated
    (intervalMappingEdgeOfVertex
      (F2.coconeTransformationVertex (F2.coherentDiagramTotalCocone F))).toTruncated
    (constantFunctorEdge (A := (SSet.uliftFunctor.{u + 1, u}).obj B)
      (standardCoconeKanLegEdge F G i j e).toTruncated)
    (coconeStandardVertexUnit_square i j e) rfl rfl rfl
    (congrArg (fun z => functorVertex
      (SSet.const z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))
      (F2.coherentDiagramTotalCocone_vertex G))
    rfl (coconeTransformationPointAt_edge (F2.coherentDiagramTotalCocone G)
      (F2.coherentDiagramTotalCocone_vertex G)).symm rfl rfl

/-- 同じ元の底変換の全空間 Kan 辺と、元の頂点脚の共役辺は同じ Hom 類。 -/
lemma standardCoconeKanLeg_homMk :
    homMk (totalKanNativeEdge F G (coherentTransformationTotalKanMap F G
      (intervalMappingVertexOfEdge (coconeWholeEdgeBottom q d e)))).toTruncated =
        homMk (standardCoconeKanLegEdge F G i j e).toTruncated := by
  apply totalKanNativeEdge_homMk_of_unit_square F G
    (intervalMappingVertexOfEdge (coconeWholeEdgeBottom q d e))
    (standardCoconeKanLegEdge F G i j e)
  rw [show intervalMappingEdgeOfVertex
    (intervalMappingVertexOfEdge (coconeWholeEdgeBottom q d e)) = coconeWholeEdgeBottom q d e from
      (intervalMappingEdgeVertexEquiv _ _).symm_apply_apply _]
  exact standardCoconeKanLeg_unit_square F G i j e

end SerrePositivity.InfinityCategories.HomotopyLimits
