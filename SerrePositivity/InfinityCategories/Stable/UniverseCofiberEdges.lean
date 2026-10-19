module
public import SerrePositivity.InfinityCategories.Stable.UniverseVertexClosure
public import SerrePositivity.InfinityCategories.Stable.CofiberLocalizingBaseChange

/-! # 実 cofiber 分母の宇宙不変性

概要：指定辺の実 cofiber 四角形を持ち上げ、実分母条件の宇宙不変性を示す。
方針：底辺・cofiber 頂点・普遍性を厳密に保持し、実安定閉包の宇宙比較を適用する。
規約：元の辺に安定性から cofiber を選ぶ。使われ方：native 分母と共通宇宙の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
variable {X : SSet.{u}}

/-- 指定実辺の cofiber 四角形を全ての単体を保持して持ち上げる。 -/
def CofiberSquare.ulift {x y : X _⦋0⦌}
    {f : Truncated.Edge (X := (truncation 2).obj X) x y} (s : CofiberSquare f) :
    CofiberSquare (X := (SSet.uliftFunctor.{v, u}).obj X) (uliftEdge.{u, v} f) where
  toZeroTriangle := ZeroTriangle.ulift s.toZeroTriangle
  bottom_edge := by
    change squareBottomEdge ≫ uliftSquare s.square = _
    rw [uliftSquare_bottomEdge, s.bottom_edge]
    exact (uliftEdge_yoneda f).symm
  isPushout := (isPushoutSquare_iff_ulift s.square).mp s.isPushout

/-- 持ち上げた cofiber 四角形の終点は元の cofiber 頂点の ULift。 -/
lemma CofiberSquare.ulift_cofiber {x y : X _⦋0⦌}
    {f : Truncated.Edge (X := (truncation 2).obj X) x y} (s : CofiberSquare f) :
    s.ulift.cofiber = (ULift.up s.cofiber : ((SSet.uliftFunctor.{v, u}).obj X) _⦋0⦌) := rfl

/-- 実辺の指定 cofiber 分母条件は宇宙持ち上げで保存・反映される。 -/
theorem cofiberStableEdges_ulift_iff [Quasicategory X] [IsStable X]
    (P : Set (X _⦋0⦌)) {x y : X _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj X) x y) :
    (uliftEdge.{u, v} f).edge ∈ cofiberLocalizingEdges (X := (SSet.uliftFunctor.{v, u}).obj X)
      {z | StableVertexClosure (ULift.up '' P) z} ↔
      f.edge ∈ cofiberLocalizingEdges {z | StableVertexClosure P z} := by
  let s := chosenCofiberSquare f
  exact (cofiberStableEdges_edge_mem_iff _ s.ulift).trans
    ((stableVertexClosure_ulift_iff.{u, v} P s.cofiber).trans
      (cofiberStableEdges_edge_mem_iff P s).symm)

end SerrePositivity.InfinityCategories
