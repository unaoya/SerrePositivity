module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-!
概要：同じ実際の可逆辺が与える同型を端点の表示によらず同定する。
方針：辺の両端を回収して端点と辺の等式を消去する。
規約：辺の代表とそのホモトピー類を変更しない。
使われ方：合成比較の第二面と元の指定三角形の同型の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 実際の辺が等しければ、その可逆性から作る同型も型を含めて等しい。 -/
lemma invertibleEdgeIso_heq_of_edge_eq {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (a : X.Edge x y) (b : X.Edge x' y')
    [IsInvertibleEdge a.toTruncated] [IsInvertibleEdge b.toTruncated]
    (h : a.edge = b.edge) :
    HEq (asIso (SSet.Truncated.HomotopyCategory.homMk a.toTruncated))
      (asIso (SSet.Truncated.HomotopyCategory.homMk b.toTruncated)) := by
  have hx : x = x' := a.src_eq.symm.trans ((congrArg (X.δ 1) h).trans b.src_eq)
  have hy : y = y' := a.tgt_eq.symm.trans ((congrArg (X.δ 0) h).trans b.tgt_eq)
  subst x'
  subst y'
  have hab : a = b := by
    apply SSet.Edge.ext
    exact h
  subst b
  rfl

end SerrePositivity.InfinityCategories.F2
