module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialFiberEdgeVertex
public import SerrePositivity.InfinityCategories.F1.LeftFibrationInitialPiZero
public import SerrePositivity.InfinityCategories.F1.PinchedLeftPiZeroVertex

/-!
概要：始対象を持つ left fibration の fiber の Hom 表示を、全空間の実際の辺で計算する。
方針：その辺の比較 span の点を評価し、基底側の coslice の辺の計算を適用する。
規約：同値逆の選択による表示ではなく、任意の指定した全空間の辺の射影の類を得る。
使われ方：部分余極限の比較辺と固定終点余錐空間の π₀ の同値の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
  {c d : E _⦋0⦌}

/-- 指定した基底の頂点との等式で、全空間の頂点を fiber の零単体として表示する。 -/
def initialFiberVertexAt (d : E _⦋0⦌) (y : B _⦋0⦌)
    (hy : p.app (Opposite.op ⦋0⦌) d = y) : (vertexFiber p y) _⦋0⦌ :=
  ⟨d, hy.trans (pinchedConstant_zero y).symm⟩

/-- 終点の表示を正規化した射影辺。 -/
def initialFiberEdgeProjectionAt (e : E.Edge c d) (y : B _⦋0⦌)
    (hy : p.app (Opposite.op ⦋0⦌) d = y) : B.Edge (p.app (Opposite.op ⦋0⦌) c) y :=
  ⟨(e.map p).edge, (e.map p).src_eq, (e.map p).tgt_eq.trans hy⟩

/-- 始対象からの実際の辺の終点の fiber 類は、射影した辺のホモトピー類に対応する。 -/
lemma leftFibrationInitialFiberPiZeroEquiv_edge (hc : IsInitialVertex c) (e : E.Edge c d) :
    leftFibrationInitialFiberPiZeroEquiv p c hc (p.app (Opposite.op ⦋0⦌) d)
        (SSet.π₀.mk (initialFiberEdgeEndpoint p)) =
      SSet.Truncated.HomotopyCategory.homMk (e.map p).toTruncated := by
  have h := leftFibrationInitialFiberPiZeroEquiv_evaluation p c hc
    (p.app (Opposite.op ⦋0⦌) d) (SSet.π₀.mk (initialFiberEdgeTotalVertex p e))
  change leftFibrationInitialFiberPiZeroEquiv p c hc (p.app (Opposite.op ⦋0⦌) d)
      (SSet.π₀.mk ((leftFibrationInitialEvaluation p c
        (p.app (Opposite.op ⦋0⦌) d)).app (Opposite.op ⦋0⦌)
          (initialFiberEdgeTotalVertex p e))) = _ at h
  rw [initialFiberEdgeTotalVertex_evaluation] at h
  refine h.trans ?_
  change pinchedHomLeftPiZeroEquiv (p.app (Opposite.op ⦋0⦌) c)
    (p.app (Opposite.op ⦋0⦌) d)
      (SSet.mapπ₀ (pinchedLeftCosliceFiberIso _ _).inv
        (SSet.π₀.mk (initialFiberEdgeBaseVertex p e))) = _
  rw [stableCosliceFiberPiZeroEquiv_mk, initialFiberEdgeBaseVertex_edge]

/-- 任意の指定した終点の表示でも、fiber の Hom 同値は正規化した射影辺の類を与える。 -/
lemma leftFibrationInitialFiberPiZeroEquiv_edgeAt (hc : IsInitialVertex c)
    (e : E.Edge c d) (y : B _⦋0⦌) (hy : p.app (Opposite.op ⦋0⦌) d = y) :
    leftFibrationInitialFiberPiZeroEquiv p c hc y
        (SSet.π₀.mk (initialFiberVertexAt p d y hy)) =
      SSet.Truncated.HomotopyCategory.homMk
        (initialFiberEdgeProjectionAt p e y hy).toTruncated := by
  cases hy
  exact leftFibrationInitialFiberPiZeroEquiv_edge p hc e

end
end SerrePositivity.InfinityCategories.HomotopyLimits
