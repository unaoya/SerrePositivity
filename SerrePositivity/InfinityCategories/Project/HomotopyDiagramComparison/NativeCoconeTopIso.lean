module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.NativeCoconeIsoRepresentative

/-!
概要：同じ coslice 同型の代表辺の頂点変換を、同じ射を持つ同型として保持する。
方針：元の可逆辺を全余錐の族と頂点制限へ写す。
規約：各点で選択した代表を変更せず、自然な族の存在は要求しない。
使われ方：実際の余極限脚と標準余極限脚の可換式の合成。
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
variable {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} {q d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p}
  (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) q d)

/-- 同じ元の coslice 同型の代表を全余錐へ写した辺は可逆。 -/
lemma nativeCoconeIsoWholeEdge_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).obj X)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeFunctorEdge (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoRepresentative e)).toTruncated := by
  have h := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoRepresentative_isInvertible e).map
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeFunctorFamily p)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoRepresentative e).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeFunctorFamily p)))
    (f := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeFunctorEdge (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoRepresentative e)).toTruncated) rfl).mp h

/-- 同じ元の coslice 同型の代表の頂点変換は可逆。 -/
lemma nativeCoconeIsoTopEdge_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (ihom K).obj X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWholeEdgeTop q d
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeFunctorEdge (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoRepresentative e)).toTruncated).toTruncated := by
  have h := (nativeCoconeIsoWholeEdge_isInvertible e).map
    ((pre (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeRightApexVertex K) : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0])).app X)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeFunctorEdge (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoRepresentative e)).toTruncated.map
      ((truncation 2).map
        ((pre (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeRightApexVertex K) : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0])).app X)))
    (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWholeEdgeTop q d
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeFunctorEdge (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoRepresentative e)).toTruncated).toTruncated)
    rfl).mp h

/-- 同じ元の coslice 比較辺の頂点変換を、その同じ Hom 類を持つ同型として保持。 -/
def nativeCoconeIsoTopIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := (ihom K).obj X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const q.vertex)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const d.vertex)) := by
  have : IsIso (homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWholeEdgeTop q d
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeFunctorEdge (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoRepresentative e)).toTruncated).toTruncated) :=
    nativeCoconeIsoTopEdge_isInvertible e
  exact asIso (homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWholeEdgeTop q d
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeFunctorEdge (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoRepresentative e)).toTruncated).toTruncated)

/-- 元の頂点同型の順方向は、同じ元の代表辺の頂点変換の類そのもの。 -/
lemma nativeCoconeIsoTopIso_hom :
    (nativeCoconeIsoTopIso e).hom = homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWholeEdgeTop q d
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeFunctorEdge (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoRepresentative e)).toTruncated).toTruncated := rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
