module

public import SerrePositivity.InfinityCategories.F2.CatTetrahedronWhiskerEdges

/-!
概要：正規化した二面の指定辺と元の精密化の一次単体の一致。
方針：両端の表示変更が辺の一次単体を保つことを使う。
規約：同じ六関手で表した辺を比較する。
使われ方：四面の正方形を端点の定義を展開せずに輸送する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：面 013 の端点を揃えても元の精密化の辺と同じ一次単体。
方針：指定一次単体による辺の定義を読む。
規約：一単体の代表を変更しない。
使われ方：指定辺の正方形の四隅の同時輸送。 -/
lemma catInfinityTetrahedronTriangle013_edge (s : CatInfinity.{u} _⦋3⦌) :
    (catInfinityTetrahedronEdge s coherentTetrahedronRefine013).edge =
      (catInfinityTetrahedronTriangle013 s).edge :=
  by rfl
/-- 概要：面 023 の端点を揃えても元の精密化の辺と同じ一次単体。
方針：指定一次単体による辺の定義を読む。
規約：一単体の代表を変更しない。
使われ方：指定辺の正方形の四隅の同時輸送。 -/
lemma catInfinityTetrahedronTriangle023_edge (s : CatInfinity.{u} _⦋3⦌) :
    (catInfinityTetrahedronEdge s coherentTetrahedronRefine023).edge =
      (catInfinityTetrahedronTriangle023 s).edge :=
  by rfl

end SerrePositivity.InfinityCategories.F2
