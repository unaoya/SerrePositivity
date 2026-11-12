module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialFiberEdgeVertex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibrationInitialPiZero
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.PinchedLeftPiZeroVertex

/-!
概要：始対象を持つ left fibration の fiber の Hom 表示を、全空間の実際の辺で計算する。
方針：その辺の比較 span の点を評価し、基底側の coslice の辺の計算を適用する。
規約：同値逆の選択による表示ではなく、任意の指定した全空間の辺の射影の類を得る。
使われ方：部分余極限の比較辺と固定終点余錐空間の π₀ の同値の照合。

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
variable {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
  {c d : E _⦋0⦌}

/-- 指定した基底の頂点との等式で、全空間の頂点を fiber の零単体として表示する。 -/
def initialFiberVertexAt (d : E _⦋0⦌) (y : B _⦋0⦌)
    (hy : p.app (Opposite.op ⦋0⦌) d = y) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p y) _⦋0⦌ :=
  ⟨d, hy.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero y).symm⟩

/-- 終点の表示を正規化した射影辺。 -/
def initialFiberEdgeProjectionAt (e : E.Edge c d) (y : B _⦋0⦌)
    (hy : p.app (Opposite.op ⦋0⦌) d = y) : B.Edge (p.app (Opposite.op ⦋0⦌) c) y :=
  ⟨(e.map p).edge, (e.map p).src_eq, (e.map p).tgt_eq.trans hy⟩

/-- 始対象からの実際の辺の終点の fiber 類は、射影した辺のホモトピー類に対応する。 -/
lemma leftFibrationInitialFiberPiZeroEquiv_edge (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex c) (e : E.Edge c d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialFiberPiZeroEquiv p c hc (p.app (Opposite.op ⦋0⦌) d)
        (SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialFiberEdgeEndpoint p)) =
      SSet.Truncated.HomotopyCategory.homMk (e.map p).toTruncated := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialFiberPiZeroEquiv_evaluation p c hc
    (p.app (Opposite.op ⦋0⦌) d) (SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialFiberEdgeTotalVertex p e))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialFiberPiZeroEquiv p c hc (p.app (Opposite.op ⦋0⦌) d)
      (SSet.π₀.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation p c
        (p.app (Opposite.op ⦋0⦌) d)).app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialFiberEdgeTotalVertex p e))) = _ at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialFiberEdgeTotalVertex_evaluation] at h
  refine h.trans ?_
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftPiZeroEquiv (p.app (Opposite.op ⦋0⦌) c)
    (p.app (Opposite.op ⦋0⦌) d)
      (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftCosliceFiberIso _ _).inv
        (SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialFiberEdgeBaseVertex p e))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stableCosliceFiberPiZeroEquiv_mk, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialFiberEdgeBaseVertex_edge]

/-- 任意の指定した終点の表示でも、fiber の Hom 同値は正規化した射影辺の類を与える。 -/
lemma leftFibrationInitialFiberPiZeroEquiv_edgeAt (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex c)
    (e : E.Edge c d) (y : B _⦋0⦌) (hy : p.app (Opposite.op ⦋0⦌) d = y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialFiberPiZeroEquiv p c hc y
        (SSet.π₀.mk (initialFiberVertexAt p d y hy)) =
      SSet.Truncated.HomotopyCategory.homMk
        (initialFiberEdgeProjectionAt p e y hy).toTruncated := by
  cases hy
  exact leftFibrationInitialFiberPiZeroEquiv_edge p hc e

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
