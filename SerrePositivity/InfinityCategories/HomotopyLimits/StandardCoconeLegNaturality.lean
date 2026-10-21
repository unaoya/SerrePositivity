module

public import SerrePositivity.InfinityCategories.HomotopyLimits.StandardCoconeKanLeg

/-!
概要：同じ元の頂点比較と実際の頂点脚・標準 Kan 脚の可換式を回収する。
方針：共役辺の同じ Hom 類の式から、元の始点比較の両逆を相殺する。
規約：元の両端比較・元の頂点脚・同じ標準 Kan 辺を保持する。
使われ方：元の各脚の可換式から有限全錐の関手同型を構成する。
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

/-- 同じ始点比較・終点比較の間で、元の実際の頂点脚と標準 Kan 脚は可換。 -/
lemma standardCoconeKanLeg_naturality {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    {q : JoinCocone F} {d : JoinCocone G}
    (i : VertexIso (X := sliceUnder F) q (F2.coherentDiagramTotalCocone F))
    (j : VertexIso (X := sliceUnder G) d (F2.coherentDiagramTotalCocone G))
    (e : SSet.Truncated.Edge
      (X := (truncation 2).obj ((ihom (join ((SSet.uliftFunctor.{u + 1, u}).obj B)
        (Δ[0] : SSet.{u + 1}))).obj SpaceInfinity.{u}))
      (functorVertex q.val) (functorVertex d.val)) :
    (nativeCoconeApexIso i).hom ≫ homMk (totalKanNativeEdge F G
      (coherentTransformationTotalKanMap F G
        (intervalMappingVertexOfEdge (coconeWholeEdgeBottom q d e)))).toTruncated =
    homMk (coconeWholeEdgeApex q d e).toTruncated ≫ (nativeCoconeApexIso j).hom ≫
      eqToHom (congrArg HomotopyCategory.mk (F2.coherentDiagramTotalCocone_vertex G)) := by
  rw [standardCoconeKanLeg_homMk F G i j e, standardCoconeKanLegEdge_homMk]
  simp only [coconeStandardVertexHom, Category.assoc, Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories.HomotopyLimits
