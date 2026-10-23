module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorPrismFiber

/-!
概要：関手の辺の頂点評価は、端点の表示変更によらず元の一単体の評価そのもの。
方針：元の辺の評価と端点の正規化を、一単体で分離する。
規約：大きな分類写像の端点を再展開せず、同じ元の一単体を保持する。
使われ方：結合区間族の辺を既存の prism と照合する際の境界。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の関手の辺を頂点で評価した一単体は、その同じ一単体の評価写像による像。 -/
lemma functorEdgeAt_edge_simplex {B X : SSet.{u}} {F G : B ⟶ X}
    (e : Edge (functorVertex F) (functorVertex G)) (b : B _⦋0⦌) :
    (functorEdgeAt e b).edge = (evaluateFunctorAt (Y := X) b).app (Opposite.op ⦋1⦌) e.edge := rfl

end SerrePositivity.InfinityCategories
