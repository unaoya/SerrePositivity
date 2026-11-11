module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.StandardCoconeKanLeg

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
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SSet.Truncated.HomotopyCategory

/-- 同じ始点比較・終点比較の間で、元の実際の頂点脚と標準 Kan 脚は可換。 -/
lemma standardCoconeKanLeg_naturality {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    {q : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G}
    (i : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) q (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone F))
    (j : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder G) d (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone G))
    (e : SSet.Truncated.Edge
      (X := (truncation 2).obj ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join ((SSet.uliftFunctor.{u + 1, u}).obj B)
        (Δ[0] : SSet.{u + 1}))).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex q.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d.val)) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeApexIso i).hom ≫ homMk (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanNativeEdge F G
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransformationTotalKanMap F G
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWholeEdgeBottom q d e)))).toTruncated =
    homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWholeEdgeApex q d e).toTruncated ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeApexIso j).hom ≫
      eqToHom (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone_vertex G)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.standardCoconeKanLeg_homMk F G i j e, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.standardCoconeKanLegEdge_homMk]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeStandardVertexHom, Category.assoc, Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
