module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.NativeCoconeTopIso

/-!
概要：元の全余錐の脚の正方形を、両端で選んだ標準余錐の変換へ移す。
方針：同じ coslice 比較の頂点同型を使い、元の頂点脚を共役する。
規約：底脚・頂点脚・両端の比較代表を固定し、比較の自然性を仮定しない。
使われ方：実際の前層余極限の脚と標準全空間余極限の脚の照合。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SSet.Truncated.HomotopyCategory
variable {K X : SSet.{u}} [Quasicategory X] {p r : K ⟶ X}
  {q q' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p} {d d' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r}
  (i : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) q q') (j : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder r) d d')
  (e : SSet.Truncated.Edge
    (X := (truncation 2).obj ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).obj X))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex q.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d.val))

/-- 元の全余錐の頂点脚を、同じ両端比較の頂点同型で標準頂点間へ移す。 -/
def coconeStandardApexHom :
    HomotopyCategory.mk (X := (ihom K).obj X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const q'.vertex)) ⟶
    HomotopyCategory.mk (X := (ihom K).obj X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const d'.vertex)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoTopIso i).inv ≫
    homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWholeEdgeTop q d e).toTruncated ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoTopIso j).hom

/-- 元の底脚と両端の標準余錐変換は、同じ共役された頂点脚について可換。 -/
lemma coconeStandardUnit_square :
    homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWholeEdgeBottom q d e).toTruncated ≫
      homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationVertex d')).toTruncated =
    homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationVertex q')).toTruncated ≫
      coconeStandardApexHom i j e := by
  have hi := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeFunctorEdge_unit_square (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoRepresentative i)
  have hj := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeFunctorEdge_unit_square (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoRepresentative j)
  change _ = _ ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoTopIso i).hom at hi
  change _ = _ ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoTopIso j).hom at hj
  rw [hj, hi]
  simpa only [coconeStandardApexHom, Category.assoc, Iso.hom_inv_id_assoc] using
    congrArg (fun a => a ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoTopIso j).hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWholeEdge_square q d e)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
