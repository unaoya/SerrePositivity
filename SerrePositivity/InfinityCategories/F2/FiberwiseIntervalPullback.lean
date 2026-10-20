module

public import SerrePositivity.InfinityCategories.F2.FiberwiseFunctorSpace

/-!
概要：同じ底の頂点を共有する path による、fiber ごとの二段の引き戻し模型。
方針：定値底の区間関手の始点・終点を、元の二射で順に引き戻す。
規約：比較は二つの元の入力と path 全体を変更しない。
使われ方：一般 coherent な cospan の有限極限と filtered 余極限の交換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E D H B : SSet.{u}} (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H)

/-- 概要：底を固定した path で第一射を置換する。
方針：始点評価を元の第一射に沿って引き戻す。
規約：第一座標は底を固定した path。使われ方：fiber ごとの path 引き戻しの第一段。 -/
def fiberwiseIntervalReplacement : SSet.{u} := pullback (fiberwiseIntervalEndpoint p 0) f

/-- 概要：底を固定した path 置換の終点評価。
方針：第一座標を終点で評価する。
規約：元の全空間 H への射。使われ方：第二射との引き戻し。 -/
def fiberwiseIntervalReplacementEndpoint : fiberwiseIntervalReplacement p f ⟶ H :=
  pullback.fst (fiberwiseIntervalEndpoint p 0) f ≫ fiberwiseIntervalEndpoint p 1

/-- 概要：同じ底の fiber 内で指定した二射を結ぶ path の全空間。
方針：底を固定した path 置換の終点を第二射で引き戻す。
規約：二つの入力は元の指定射。使われ方：coherent な fiber ごとの引き戻し。 -/
def fiberwiseIntervalPullback : SSet.{u} :=
  pullback (fiberwiseIntervalReplacementEndpoint p f) g

/-- 概要：底を固定した path 置換を元の全 path 置換へ送る。
方針：path の底を忘れ、第一入力は恒等で保つ。
規約：元の path 座標を保持。使われ方：全空間の path 引き戻しへの比較の第一段。 -/
def fiberwiseIntervalReplacementComparison : fiberwiseIntervalReplacement p f ⟶
    intervalReplacement f :=
  pullback.map (fiberwiseIntervalEndpoint p 0) f ((intervalEndpointNatTrans 0).app H) f
    (pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (constantDiagram Δ[1] B)) (𝟙 E) (𝟙 H)
    (by rw [Category.comp_id]; rfl) (by rw [Category.comp_id, Category.id_comp])

/-- 概要：第一段の比較は終点評価を厳密に保つ。
方針：引き戻しの第一射影を計算する。
規約：同じ元の H。使われ方：第二段の引き戻しの指定可換条件。 -/
lemma fiberwiseIntervalReplacementComparison_endpoint :
    fiberwiseIntervalReplacementComparison p f ≫ intervalReplacementEndpoint f =
      fiberwiseIntervalReplacementEndpoint p f := by
  change fiberwiseIntervalReplacementComparison p f ≫
    (pullback.fst ((intervalEndpointNatTrans 0).app H) f ≫
      (intervalEndpointNatTrans 1).app H) = _
  rw [← Category.assoc, fiberwiseIntervalReplacementComparison, pullback.map,
    pullback.lift_fst, Category.assoc]
  rfl

/-- 概要：fiber ごとの path 引き戻しから全空間の path 引き戻しへの実際の比較。
方針：第一段の比較と第二入力の恒等射を引き戻す。
規約：指定した元の二射と path 全体を保持。使われ方：filtered 引き戻し交換の比較射。 -/
def fiberwiseIntervalPullbackComparison : fiberwiseIntervalPullback p f g ⟶
    intervalPullback f g :=
  pullback.map (fiberwiseIntervalReplacementEndpoint p f) g (intervalReplacementEndpoint f) g
    (fiberwiseIntervalReplacementComparison p f) (𝟙 D) (𝟙 H)
    (by rw [Category.comp_id, fiberwiseIntervalReplacementComparison_endpoint])
    (by rw [Category.comp_id, Category.id_comp])

end SerrePositivity.InfinityCategories.F2
