module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.NativeConeIsoRepresentative
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FiniteFamilyProductComparison

/-!
概要：元の有限関手積錐の比較を、一つの固定した頂点辺と元の全脚の合成三角形にする。
方針：同じ slice 内の比較辺を取り、元の頂点と全脚の端点表示だけを厳密に揃える。
規約：元の全脚の全一単体と元の比較三角形を保持する。
使われ方：元の P_Σ 評価錐の脚を、反復積射影と頂点比較の合成へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {B : SSet.{u}} {J : Type u} [Finite J] [Nonempty J]
  (G : J → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorDiagram G)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c)
  (A : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (hA : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex A)

/-- 元の slice 比較の同じ代表を、全頂点と全脚で共有する。 -/
def finiteFamilyConeComparisonEdge :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeConeIsoRepresentative (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorProductConeComparison G c hc)

/-- 元の同じ slice 比較を頂点に写した、元の評価関手と積関手の間の実際の辺。 -/
def finiteFamilyConeComparisonApexEdge :
    SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex A) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyCoherentProduct G)) :=
  (SSet.Edge.ofTruncated ((finiteFamilyConeComparisonEdge G c hc).map
    ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorDiagram G))))).ofEq
      hA (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorProductCone_vertex G)

/-- 元の全錐の脚の全一単体を、元の頂点関手と元の各成分関手の端点表示で保持する。 -/
def finiteFamilyOriginalConeLeg (j : J) : SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex A) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (G j)) :=
  (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c
    (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j))))).ofEq hA (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorDiagram_vertex G j)

/-- 元の積全錐の脚の全一単体を、元の反復積関手と元の成分関手の端点表示で保持する。 -/
def finiteFamilyProductConeLeg (j : J) :
    SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyCoherentProduct G)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (G j)) :=
  (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorProductCone G)
    (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j))))).ofEq
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorProductCone_vertex G) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorDiagram_vertex G j)

/-- 元の同じ頂点比較辺と元の各積脚・評価脚は、全三面を持つ元の合成三角形を成す。 -/
def finiteFamilyConeComparisonLegTriangle (j : J) : SSet.Truncated.Edge.CompStruct
    (finiteFamilyConeComparisonApexEdge G c hc A hA).toTruncated
    (finiteFamilyProductConeLeg G j).toTruncated
    (finiteFamilyOriginalConeLeg G c A hA j).toTruncated := by
  let T := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeConeComparisonLegTriangle (finiteFamilyConeComparisonEdge G c hc)
    (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j)))
  exact ⟨T.simplex, T.d₂, T.d₀, T.d₁⟩

/-- 元の同じ頂点比較辺は、元の slice 比較の可逆性を保持する。 -/
lemma finiteFamilyConeComparisonApexEdge_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (finiteFamilyConeComparisonApexEdge G c hc A hA) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (finiteFamilyConeComparisonApexEdge G c hc A hA).toTruncated)
    (f := (finiteFamilyConeComparisonEdge G c hc).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorDiagram G)))) rfl).mpr
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeConeIsoRepresentative_isInvertible
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorProductConeComparison G c hc)).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorDiagram G))

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
