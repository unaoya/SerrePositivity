module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeComparisonEdge
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialFiberEdgePiZero
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeMappingPiZero

/-!
概要：余極限錐全体からの coherent な比較を、固定終点余錐空間の Hom 同値で計算する。
方針：元の余錐圏での実際の辺に、始対象を持つ left fibration の零単体の計算を適用する。
規約：元の比較余錐の頂点と脚を指定したまま、選択によらないホモトピー類を得る。
使われ方：部分余極限対象の span と、共通部分の余錐空間での整合性の照合。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone c.val)

/-- 比較余錐を元の図式へ制限し、同じ指定頂点への余錐空間の点とする。 -/
def coconeComparisonFiberVertex : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p d.vertex) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialFiberVertexAt (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeComparisonTarget c d) d.vertex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeComparisonTarget_vertex c d)

/-- 比較余錐の制限の類は、部分余極限の頂点からの実際の比較脚のホモトピー類に対応する。 -/
lemma coconeMappingSpacePiZeroEquiv_comparison (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpacePiZeroEquiv c hc d.vertex (SSet.π₀.mk (coconeComparisonFiberVertex c d)) =
      SSet.Truncated.HomotopyCategory.homMk (d.leg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0])) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.leftFibrationInitialFiberPiZeroEquiv_edgeAt (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) hc
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeComparisonEdge c d) d.vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeComparisonTarget_vertex c d)
  refine h.trans ?_
  apply congrArg SSet.Truncated.HomotopyCategory.homMk
  apply SSet.Truncated.Edge.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeComparisonEdge_projection c d

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
