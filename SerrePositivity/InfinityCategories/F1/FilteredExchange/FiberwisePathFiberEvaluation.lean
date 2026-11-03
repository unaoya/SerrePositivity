module

public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.Core.CatInfinity.ConstantDiagram
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseFunctorFiber
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalDiagram

/-!
概要：底を固定した path の fiber 同型は元の両端評価を保持する。
方針：内部 Hom の包含式と端点評価の自然性を使う。
規約：元の同じ底の頂点を固定する。
使われ方：path 引き戻しの各 fiber を元の値の引き戻しへ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：path の fiber 同型は各端点の元の全空間への包含を保つ。
方針：端点評価の自然性を全関手空間への包含式と合成する。
規約：0 が始点、1 が終点。使われ方：fiber 比較の両端条件。 -/
lemma fiberwiseFunctorFiberIso_interval_endpoint {E B : SSet.{u}}
    (p : E ⟶ B) (b : B _⦋0⦌) (e : Fin 2) :
    (fiberwiseFunctorFiberIso p Δ[1] b).hom ≫
      (intervalEndpointNatTrans e).app (vertexFiber p b) ≫ vertexFiberι p b =
      vertexFiberι (fiberwiseFunctorProjection p Δ[1]) b ≫ fiberwiseIntervalEndpoint p e := by
  have hn : (ihom (Δ[1] : SSet.{u})).map (vertexFiberι p b) ≫
      (intervalEndpointNatTrans e).app E =
      (intervalEndpointNatTrans e).app (vertexFiber p b) ≫ vertexFiberι p b :=
    (intervalEndpointNatTrans e).naturality (vertexFiberι p b)
  rw [← hn, ← Category.assoc, fiberwiseFunctorFiberIso_hom_ι, Category.assoc]
  rfl

/-- 概要：fiber 内の path を全空間へ戻す逆同型も元の端点を保つ。
方針：順方向の端点式を同型の逆で前合成する。
規約：元の fiber の包含。使われ方：fiber 比較の逆射の両端条件。 -/
lemma fiberwiseFunctorFiberIso_inv_interval_endpoint {E B : SSet.{u}}
    (p : E ⟶ B) (b : B _⦋0⦌) (e : Fin 2) :
    (fiberwiseFunctorFiberIso p Δ[1] b).inv ≫
      vertexFiberι (fiberwiseFunctorProjection p Δ[1]) b ≫ fiberwiseIntervalEndpoint p e =
      (intervalEndpointNatTrans e).app (vertexFiber p b) ≫ vertexFiberι p b := by
  rw [← fiberwiseFunctorFiberIso_interval_endpoint p b e, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

end SerrePositivity.InfinityCategories.F2
