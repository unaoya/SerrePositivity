module
public import SerrePositivity.InfinityCategories.Core.SquareHomotopyCategory
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy
public import SerrePositivity.InfinityCategories.Core.EquivalencePath

/-!
概要：四つの実 suspension 面の引き戻し性から、元の押し出しの像の普遍性を導く。
方針：全 cospan の厳密保存、同じ θ と対角合成、元の入力面の極限錐を接続する。
規約：標的の零対象や一般安定性は仮定しない。使われ方：一般切除・loop 同値判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma squareBottomArrow_functorEdge_edge {X : SSet.{u}}
    {a b : ((ihom (Δ[1] : SSet.{u})).obj X) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[1] : SSet.{u})).obj X)) a b) :
    (squareBottomArrow (uncurry (SSet.yonedaEquiv.symm e.edge))).edge =
      intervalFunctorVertexEdge a := by
  have hv := (functorVertex_uncurry_zero e.edge).trans e.src_eq
  have h := congrArg intervalFunctorVertexEdge hv
  erw [intervalFunctorVertexEdge_functorVertex] at h
  erw [squareBottomArrow_edge]
  exact h

end SerrePositivity.InfinityCategories
