module

public import SerrePositivity.InfinityCategories.F1.Fibrations.InvertibleTriangleCancellation

/-!
概要：元の可逆辺の像を、同じ一単体の標準端点表示で可逆と判定する。
方針：辺全体の像を小さい補題で受け取り、端点の大きい定義の展開を分離する。
規約：指定された元の辺と指定された元の射そのもの。
使われ方：二回目の比較辺の底変換による前合成の可逆性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の可逆辺の元の射による像は、同じ一単体の標準端点表示でも可逆。 -/
lemma isInvertibleEdge_edgeOfSimplex_map {X Y : SSet.{u}} (f : X ⟶ Y)
    {x y : X _⦋0⦌} (e : SSet.Edge x y) (he : IsInvertibleEdge e.toTruncated) :
    IsInvertibleEdge (edgeOfSimplex (f.app (Opposite.op ⦋1⦌) e.edge)) :=
  isInvertibleEdge_edgeOfSimplex (e.map f) (he.map f)

end SerrePositivity.InfinityCategories
