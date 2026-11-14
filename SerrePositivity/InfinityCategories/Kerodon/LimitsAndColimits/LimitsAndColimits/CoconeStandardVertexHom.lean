module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.NativeCoconeApexIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeStandardUnitSquare

/-!
概要：元の全余錐脚を頂点圏内で共役し、その定値像を同じ関手圏内の共役射へ照合する。
方針：同じ coslice 比較の頂点同型・元の頂点評価辺・定値 Hom の合成互換を使う。
規約：元の両端比較と全余錐の辺を保持し、自然な比較族を仮定しない。
使われ方：元の実際の余極限脚を標準全空間 Kan 脚と比較する。

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

/-- 元の右頂点評価脚を、同じ元の頂点同型で標準頂点間へ共役した射。 -/
def coconeStandardVertexHom :
    HomotopyCategory.mk (X := X) q'.vertex ⟶ HomotopyCategory.mk (X := X) d'.vertex :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeApexIso i).inv ≫ homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWholeEdgeApex q d e).toTruncated ≫
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeApexIso j).hom

/-- 元の頂点圏内の共役射の定値像は、元の関手圏内の共役射そのもの。 -/
lemma coconeStandardVertexHom_constant :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (coconeStandardVertexHom i j e) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeStandardApexHom i j e := by
  rw [coconeStandardVertexHom, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_comp,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeApexIso_constant_inv, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeApexIso_constant_hom,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWholeEdgeApex_constant_hom]
  rfl

/-- 元の頂点圏内の同じ共役射を表す、標準頂点間の一つの辺。 -/
def coconeStandardVertexEdge : SSet.Edge q'.vertex d'.vertex :=
  SSet.Edge.ofTruncated (Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _
    (coconeStandardVertexHom i j e)))

/-- 同じ標準頂点間の辺の類は、元の同じ頂点比較で共役した射。 -/
lemma coconeStandardVertexEdge_homMk :
    homMk (coconeStandardVertexEdge i j e).toTruncated = coconeStandardVertexHom i j e :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ (coconeStandardVertexHom i j e))

/-- 元の頂点共役辺の定値辺の類は、元の関手圏内の共役射そのもの。 -/
lemma coconeStandardVertexEdge_constant_hom :
    homMk (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.constantFunctorEdge (A := K) (coconeStandardVertexEdge i j e).toTruncated) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeStandardApexHom i j e := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.constantFunctorHomMap_homMk, coconeStandardVertexEdge_homMk,
    coconeStandardVertexHom_constant]

/-- 元の頂点圏内の共役辺と、元の底脚・両標準余錐変換の正方形は可換。 -/
lemma coconeStandardVertexUnit_square :
    homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWholeEdgeBottom q d e).toTruncated ≫
      homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationVertex d')).toTruncated =
    homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationVertex q')).toTruncated ≫
      homMk (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.constantFunctorEdge (A := K) (coconeStandardVertexEdge i j e).toTruncated) := by
  rw [coconeStandardVertexEdge_constant_hom]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeStandardUnit_square i j e

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
