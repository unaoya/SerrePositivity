module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberwisePathFiberEvaluation
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberwiseIntervalPullbackLift
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberwiseIntervalProjection
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap

/-!
概要：元の値の三座標を、元の全空間の path 引き戻しへ戻す。
方針：fiber 内の path を逆同型で戻し、元の両端条件を保持して持ち上げる。
規約：同じ底の頂点を固定する。
使われ方：path 引き戻しの fiber 同型の逆方向。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {T E D H B : SSet.{u}} (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H) (b : B _⦋0⦌)
  (a : T ⟶ (ihom (Δ[1] : SSet.{u})).obj (vertexFiber p b))
  (s : T ⟶ vertexFiber (f ≫ p) b) (t : T ⟶ vertexFiber (g ≫ p) b)
  (ha : a ≫ (intervalEndpointNatTrans 0).app (vertexFiber p b) =
    s ≫ vertexFiberMap (f ≫ p) p f rfl b)
  (hb : a ≫ (intervalEndpointNatTrans 1).app (vertexFiber p b) =
    t ≫ vertexFiberMap (g ≫ p) p g rfl b)

/-- 概要：fiber 内の指定三座標を元の path 引き戻しへ戻す。
方針：path の逆同型と fiber の包含を用い、元の両端式で持ち上げる。
規約：元の path を選び直さない。使われ方：fiber 同型の逆の構成。 -/
def fiberwisePullbackFiberRawLift : T ⟶ fiberwiseIntervalPullback p f g :=
  fiberwiseIntervalPullbackLift p f g
    (a ≫ (fiberwiseFunctorFiberIso p Δ[1] b).inv ≫
      vertexFiberι (fiberwiseFunctorProjection p Δ[1]) b)
    (s ≫ vertexFiberι (f ≫ p) b) (t ≫ vertexFiberι (g ≫ p) b) (by
      simp only [Category.assoc]
      rw [fiberwiseFunctorFiberIso_inv_interval_endpoint, ← Category.assoc, ha,
        Category.assoc, vertexFiberMap_ι]) (by
      simp only [Category.assoc]
      rw [fiberwiseFunctorFiberIso_inv_interval_endpoint, ← Category.assoc, hb,
        Category.assoc, vertexFiberMap_ι])

/-- 概要：戻した族の全 path は元の fiber path の逆同型による像。
方針：元の持ち上げの第一座標。規約：全時刻で一致。使われ方：逆の座標検査。 -/
lemma fiberwisePullbackFiberRawLift_path :
    fiberwisePullbackFiberRawLift p f g b a s t ha hb ≫ fiberwiseIntervalPullbackPath p f g =
      a ≫ (fiberwiseFunctorFiberIso p Δ[1] b).inv ≫
        vertexFiberι (fiberwiseFunctorProjection p Δ[1]) b :=
  fiberwiseIntervalPullbackLift_path _ _ _ _ _ _ _ _

/-- 概要：戻した族の第一入力は元の fiber 入力の包含。
方針：元の持ち上げの第二座標。規約：元の第一値。使われ方：逆の第一脚の検査。 -/
lemma fiberwisePullbackFiberRawLift_left :
    fiberwisePullbackFiberRawLift p f g b a s t ha hb ≫ fiberwiseIntervalPullbackLeft p f g =
      s ≫ vertexFiberι (f ≫ p) b := fiberwiseIntervalPullbackLift_left _ _ _ _ _ _ _ _

/-- 概要：戻した族の第二入力は元の fiber 入力の包含。
方針：元の持ち上げの第三座標。規約：元の第二値。使われ方：逆の第二脚の検査。 -/
lemma fiberwisePullbackFiberRawLift_right :
    fiberwisePullbackFiberRawLift p f g b a s t ha hb ≫ fiberwiseIntervalPullbackRight p f g =
      t ≫ vertexFiberι (g ≫ p) b := fiberwiseIntervalPullbackLift_right _ _ _ _ _ _ _ _

/-- 概要：戻した族は同じ元の底の頂点に重なる。
方針：全 path 座標の fiber の包含の底を読む。
規約：底の全単体が定値。使われ方：戻した族を元の fiber に入れる。 -/
lemma fiberwisePullbackFiberRawLift_projection :
    fiberwisePullbackFiberRawLift p f g b a s t ha hb ≫
      fiberwiseIntervalPullbackProjection p f g = SSet.const b := by
  change fiberwisePullbackFiberRawLift p f g b a s t ha hb ≫
    (fiberwiseIntervalPullbackPath p f g ≫ fiberwiseFunctorProjection p Δ[1]) = _
  rw [← Category.assoc, fiberwisePullbackFiberRawLift_path, Category.assoc, Category.assoc,
    vertexFiberι_comp, SSet.comp_const, SSet.comp_const]

end SerrePositivity.InfinityCategories.F2
