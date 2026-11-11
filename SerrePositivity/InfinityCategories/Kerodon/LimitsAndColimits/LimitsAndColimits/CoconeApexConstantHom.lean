module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ConstantPrecompositionFactor

/-!
概要：元の全余錐間の辺の頂点評価を保持し、その定値 Hom 像を元の頂点変換へ照合する。
方針：右頂点の同じ評価辺を取り、一定頂点への前合成の厳密な因子化を使う。
規約：元の全一単体と両頂点を変更せず、充填性を仮定しない。
使われ方：Space 内の実際の頂点脚の共役と、関手圏内の共役射の比較。

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
variable {K X : SSet.{u}} {p r : K ⟶ X} (q : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r)
  (e : SSet.Truncated.Edge
    (X := (truncation 2).obj ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).obj X))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex q.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d.val))

/-- 元の全余錐間の辺の右頂点評価を、元の両余錐頂点の辺として保持する。 -/
def coconeWholeEdgeApex : SSet.Edge q.vertex d.vertex :=
  (SSet.Edge.ofTruncated (e.map ((truncation 2).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeRightApexVertex K))))).ofEq
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeRightApexVertex K) q.val).trans
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.cocone_vertex_at_rightApex q))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeRightApexVertex K) d.val).trans
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.cocone_vertex_at_rightApex d))

/-- 元の頂点評価辺の定値 Hom 像は、元の同じ全余錐の頂点変換の類そのもの。 -/
lemma coconeWholeEdgeApex_constant_hom :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (homMk (coconeWholeEdgeApex q d e).toTruncated) =
      homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWholeEdgeTop q d e).toTruncated := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.constantFunctorHomMap_homMk]
  congr 1
  apply SSet.Truncated.Edge.ext
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeWholeEdgeTop_constant q d e).symm

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
