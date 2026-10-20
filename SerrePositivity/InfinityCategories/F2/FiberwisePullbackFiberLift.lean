module

public import SerrePositivity.InfinityCategories.F2.FiberwisePullbackFiberRawLift
public import SerrePositivity.InfinityCategories.F2.FiberwisePullbackFiberCoordinates

/-!
概要：元の値の三座標から、元の path 引き戻しの同じ底の fiber への持ち上げ。
方針：底への定値性で fiber に入れ、単射な包含後に各座標を検査する。
規約：元の全 path と二入力を保持する。
使われ方：path 引き戻しの fiber 同型の逆と一意性。
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

/-- 概要：元の値の指定三座標を、元の引き戻しの fiber に入れる。
方針：全空間への持ち上げの底射の定値性を使う。
規約：同じ元の b。使われ方：fiber 同型の逆の族。 -/
def fiberwisePullbackFiberLift : T ⟶ vertexFiber (fiberwiseIntervalPullbackProjection p f g) b :=
  vertexFiberLift _ b (fiberwisePullbackFiberRawLift p f g b a s t ha hb)
    (fiberwisePullbackFiberRawLift_projection p f g b a s t ha hb)

/-- 概要：fiber への持ち上げの包含は元の全空間への持ち上げ。
方針：fiber の普遍性。規約：全単体で一致。使われ方：逆の座標の検査。 -/
lemma fiberwisePullbackFiberLift_ι :
    fiberwisePullbackFiberLift p f g b a s t ha hb ≫
      vertexFiberι (fiberwiseIntervalPullbackProjection p f g) b =
      fiberwisePullbackFiberRawLift p f g b a s t ha hb := vertexFiberLift_ι _ _ _ _

/-- 概要：fiber への持ち上げは第一入力を厳密に保持。
方針：元の fiber の単射な包含後に計算。
規約：元の s。使われ方：fiber 同型の第一脚。 -/
lemma fiberwisePullbackFiberLift_left :
    fiberwisePullbackFiberLift p f g b a s t ha hb ≫ fiberwisePullbackFiberLeft p f g b = s := by
  apply (cancel_mono (vertexFiberι (f ≫ p) b)).1
  rw [Category.assoc, fiberwisePullbackFiberLeft_ι, ← Category.assoc,
    fiberwisePullbackFiberLift_ι, fiberwisePullbackFiberRawLift_left]

/-- 概要：fiber への持ち上げは第二入力を厳密に保持。
方針：元の fiber の単射な包含後に計算。
規約：元の t。使われ方：fiber 同型の第二脚。 -/
lemma fiberwisePullbackFiberLift_right :
    fiberwisePullbackFiberLift p f g b a s t ha hb ≫ fiberwisePullbackFiberRight p f g b = t := by
  apply (cancel_mono (vertexFiberι (g ≫ p) b)).1
  rw [Category.assoc, fiberwisePullbackFiberRight_ι, ← Category.assoc,
    fiberwisePullbackFiberLift_ι, fiberwisePullbackFiberRawLift_right]

/-- 概要：fiber への持ち上げは元の全 path を厳密に保持。
方針：内部 Hom の単射な包含後に、path の fiber 同型の往復を使う。
規約：全時刻で一致。使われ方：fiber 同型の path 座標。 -/
lemma fiberwisePullbackFiberLift_path :
    fiberwisePullbackFiberLift p f g b a s t ha hb ≫ fiberwisePullbackFiberPath p f g b = a := by
  have hι : (fiberwiseFunctorFiberIso p Δ[1] b).inv ≫
      vertexFiberι (fiberwiseFunctorProjection p Δ[1]) b ≫
        pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (constantDiagram Δ[1] B) =
      (ihom (Δ[1] : SSet.{u})).map (vertexFiberι p b) := by
    rw [← fiberwiseFunctorFiberIso_hom_ι, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  apply (cancel_mono ((ihom (Δ[1] : SSet.{u})).map (vertexFiberι p b))).1
  rw [Category.assoc, fiberwisePullbackFiberPath_ι, ← Category.assoc,
    fiberwisePullbackFiberLift_ι, ← Category.assoc, fiberwisePullbackFiberRawLift_path,
    Category.assoc]
  simp only [Category.assoc]
  rw [hι]

end SerrePositivity.InfinityCategories.F2
