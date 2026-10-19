module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeComparisonEdge
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialFiberEdgePiZero
public import SerrePositivity.InfinityCategories.Stable.CoconeMappingPiZero

/-!
概要：余極限錐全体からの coherent な比較を、固定終点余錐空間の Hom 同値で計算する。
方針：元の余錐圏での実際の辺に、始対象を持つ left fibration の零単体の計算を適用する。
規約：元の比較余錐の頂点と脚を指定したまま、選択によらないホモトピー類を得る。
使われ方：部分余極限対象の span と、共通部分の余錐空間での整合性の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
  (c : JoinCocone p) (d : JoinCocone c.val)

/-- 比較余錐を元の図式へ制限し、同じ指定頂点への余錐空間の点とする。 -/
def coconeComparisonFiberVertex : (coconeMappingSpace p d.vertex) _⦋0⦌ :=
  initialFiberVertexAt (sliceUnderProjection p) (coconeComparisonTarget c d) d.vertex
    (coconeComparisonTarget_vertex c d)

/-- 比較余錐の制限の類は、部分余極限の頂点からの実際の比較脚のホモトピー類に対応する。 -/
lemma coconeMappingSpacePiZeroEquiv_comparison (hc : IsColimitCone c) :
    coconeMappingSpacePiZeroEquiv c hc d.vertex (SSet.π₀.mk (coconeComparisonFiberVertex c d)) =
      SSet.Truncated.HomotopyCategory.homMk (d.leg (joinInr K Δ[0])) := by
  have h := leftFibrationInitialFiberPiZeroEquiv_edgeAt (sliceUnderProjection p) hc
    (coconeComparisonEdge c d) d.vertex (coconeComparisonTarget_vertex c d)
  refine h.trans ?_
  apply congrArg SSet.Truncated.HomotopyCategory.homMk
  apply SSet.Truncated.Edge.ext
  exact coconeComparisonEdge_projection c d

end
end SerrePositivity.InfinityCategories.HomotopyLimits
