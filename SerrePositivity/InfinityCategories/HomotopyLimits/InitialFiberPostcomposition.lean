module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialFiberEdgePiZero
public import SerrePositivity.InfinityCategories.Core.InitialUniqueness

/-!
概要：始対象を持つ left fibration の fiber の Hom 表示は、全空間の辺に沿う輸送を後合成へ送る。
方針：始対象からの辺と指定した辺の合成三角形を射影し、零単体での Hom 計算を適用する。
規約：底の辺だけでなく、始点と終点を指定した全空間の実際の辺を入力とする。
使われ方：部分余錐の頂点を span の終点へ輸送した後の、共通部分の連結成分の比較。
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
  (c : E _⦋0⦌) (hc : IsInitialVertex c)

/-- 全空間の辺に沿って終点を動かすと、fiber の Hom 表示は射影辺との後合成で変わる。 -/
lemma leftFibrationInitialFiberPiZeroEquiv_post_edge {d e : E _⦋0⦌} (k : E.Edge d e) :
    leftFibrationInitialFiberPiZeroEquiv p c hc (p.app (Opposite.op ⦋0⦌) d)
        (SSet.π₀.mk (initialFiberEdgeEndpoint p)) ≫
      SSet.Truncated.HomotopyCategory.homMk (k.map p).toTruncated =
    leftFibrationInitialFiberPiZeroEquiv p c hc (p.app (Opposite.op ⦋0⦌) e)
      (SSet.π₀.mk (initialFiberEdgeEndpoint p)) := by
  have : Quasicategory E := quasicategory_of_innerFibration p
  obtain ⟨g⟩ := hc.nonempty_edge d
  let h := SSet.Truncated.Edge.comp g k.toTruncated
  rw [leftFibrationInitialFiberPiZeroEquiv_edge p hc (SSet.Edge.ofTruncated g),
    leftFibrationInitialFiberPiZeroEquiv_edge p hc (SSet.Edge.ofTruncated h)]
  exact SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    ((SSet.Truncated.Edge.compStruct g k.toTruncated).map ((truncation 2).map p))

/-- 始点と終点の表示を指定した、全空間の辺の基底への射影。 -/
def initialFiberTransportProjection {d e : E _⦋0⦌} (k : E.Edge d e)
    (a b : B _⦋0⦌) (ha : p.app (Opposite.op ⦋0⦌) d = a)
    (hb : p.app (Opposite.op ⦋0⦌) e = b) : B.Edge a b :=
  ⟨(k.map p).edge, (k.map p).src_eq.trans ha, (k.map p).tgt_eq.trans hb⟩

/-- 指定した両端の fiber でも、全空間の辺に沿う変化は射影辺との後合成になる。 -/
lemma leftFibrationInitialFiberPiZeroEquiv_post_edgeAt {d e : E _⦋0⦌} (k : E.Edge d e)
    (a b : B _⦋0⦌) (ha : p.app (Opposite.op ⦋0⦌) d = a)
    (hb : p.app (Opposite.op ⦋0⦌) e = b) :
    leftFibrationInitialFiberPiZeroEquiv p c hc a
        (SSet.π₀.mk (initialFiberVertexAt p d a ha)) ≫
      SSet.Truncated.HomotopyCategory.homMk
        (initialFiberTransportProjection p k a b ha hb).toTruncated =
    leftFibrationInitialFiberPiZeroEquiv p c hc b
      (SSet.π₀.mk (initialFiberVertexAt p e b hb)) := by
  cases ha
  cases hb
  exact leftFibrationInitialFiberPiZeroEquiv_post_edge p c hc k

end
end SerrePositivity.InfinityCategories.HomotopyLimits
