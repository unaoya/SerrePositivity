module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.UniverseVertexClosure
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberLocalizingBaseChange

/-! # 実 cofiber 分母の宇宙不変性

概要：指定辺の実 cofiber 四角形を持ち上げ、実分母条件の宇宙不変性を示す。
方針：底辺・cofiber 頂点・普遍性を厳密に保持し、実安定閉包の宇宙比較を適用する。
規約：元の辺に安定性から cofiber を選ぶ。使われ方：native 分母と共通宇宙の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}}

/-- 指定実辺の cofiber 四角形を全ての単体を保持して持ち上げる。 -/
def CofiberSquare.ulift {x y : X _⦋0⦌}
    {f : Truncated.Edge (X := (truncation 2).obj X) x y} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare f) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare (X := (SSet.uliftFunctor.{v, u}).obj X) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftEdge.{u, v} f) where
  toZeroTriangle := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangle.ulift s.toZeroTriangle
  bottom_edge := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare s.square = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare_bottomEdge, s.bottom_edge]
    exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftEdge_yoneda f).symm
  isPushout := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isPushoutSquare_iff_ulift s.square).mp s.isPushout

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberSquare (ulift)


/-- 持ち上げた cofiber 四角形の終点は元の cofiber 頂点の ULift。 -/
lemma CofiberSquare.ulift_cofiber {x y : X _⦋0⦌}
    {f : Truncated.Edge (X := (truncation 2).obj X) x y} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare f) :
    s.ulift.cofiber = (ULift.up s.cofiber : ((SSet.uliftFunctor.{v, u}).obj X) _⦋0⦌) := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberSquare (ulift_cofiber)


/-- 実辺の指定 cofiber 分母条件は宇宙持ち上げで保存・反映される。 -/
theorem cofiberStableEdges_ulift_iff [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (P : Set (X _⦋0⦌)) {x y : X _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj X) x y) :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftEdge.{u, v} f).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (X := (SSet.uliftFunctor.{v, u}).obj X)
      {z | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (ULift.up '' P) z} ↔
      f.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {z | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P z} := by
  let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare f
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_edge_mem_iff _ s.ulift).trans
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableVertexClosure_ulift_iff.{u, v} P s.cofiber).trans
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_edge_mem_iff P s).symm)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
