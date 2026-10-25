module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.RightUnitInvariance

/-!
概要：元の随伴の実単位を、固定右の全関手圏の coslice に持ち上げる。
方針：同じ代表辺を coslice 頂点として引き戻し、単位の回収を検証する。
規約：左関手の保存条件を追加の仮定にしない。
使われ方：普遍単位の空間と随伴条件の比較の基準頂点。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：固定した右関手との元の随伴の実単位を coslice 頂点へ持ち上げる。
方針：指定単位の代表辺と左関手の頂点を引き戻す。
規約：元の左右の関手と指定単位を使う。
使われ方：随伴単位の条件を満たす基準頂点。 -/
def rightUnitVertex {C D : PresentableInfinityObject.{u}}
    {w : PrRFunctorSpace D C _⦋0⦌} {L : C.obj ⟶ D.obj}
    (a : QCatAdjunction L (rightVertexFunctor w)) : RightUnitCoslice C D w _⦋0⦌ :=
  SSet.yonedaEquiv (pullback.lift (SSet.yonedaEquiv.symm
    (edgeCosliceVertex (functorEdgeOfSimplicialHomotopy (functorHomHomotopy a.unitHom))))
    (SSet.yonedaEquiv.symm (functorVertex L)) (by
      rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, edgeCosliceVertex_projection]
      rfl))

/-- 概要：指定随伴からの頂点の単位の coslice 成分は元の代表辺。
方針：引き戻しの第一射影と Yoneda の往復を計算する。
規約：一次単体の代表を保つ。
使われ方：元の指定単位の回収。 -/
lemma rightUnitVertex_slice {C D : PresentableInfinityObject.{u}}
    {w : PrRFunctorSpace D C _⦋0⦌} {L : C.obj ⟶ D.obj}
    (a : QCatAdjunction L (rightVertexFunctor w)) :
    (pullback.fst _ ((ihom C.obj).map (rightVertexFunctor w))).app (Opposite.op ⦋0⦌)
      (rightUnitVertex a) =
    edgeCosliceVertex (functorEdgeOfSimplicialHomotopy (functorHomHomotopy a.unitHom)) := by
  dsimp only [rightUnitVertex, RightUnitCoslice]
  rw [← SSet.yonedaEquiv_comp, pullback.lift_fst, Equiv.apply_symm_apply]

/-- 概要：指定随伴からの頂点の左関手の頂点は元の左関手。
方針：引き戻しの第二射影と Yoneda の往復を計算する。
規約：元の関手頂点の厳密な回収。
使われ方：単位の随伴条件の端点の照合。 -/
lemma rightUnitVertex_base {C D : PresentableInfinityObject.{u}}
    {w : PrRFunctorSpace D C _⦋0⦌} {L : C.obj ⟶ D.obj}
    (a : QCatAdjunction L (rightVertexFunctor w)) :
    (pullback.snd _ ((ihom C.obj).map (rightVertexFunctor w))).app (Opposite.op ⦋0⦌)
      (rightUnitVertex a) = functorVertex L := by
  dsimp only [rightUnitVertex, RightUnitCoslice]
  rw [← SSet.yonedaEquiv_comp, pullback.lift_snd, Equiv.apply_symm_apply]

/-- 概要：指定随伴からの頂点の左関手は元の左関手。
方針：底の頂点の計算を関手頂点の表示の逆に移す。
規約：元の単体集合の射として等しい。
使われ方：単位条件の輸送。 -/
lemma rightUnitVertex_left {C D : PresentableInfinityObject.{u}}
    {w : PrRFunctorSpace D C _⦋0⦌} {L : C.obj ⟶ D.obj}
    (a : QCatAdjunction L (rightVertexFunctor w)) :
    rightUnitLeftFunctor (rightUnitVertex a) = L := by
  unfold rightUnitLeftFunctor
  rw [rightUnitVertex_base]
  exact (functorVertexEquiv C.obj D.obj).symm_apply_apply L

/-- 概要：指定随伴からの頂点の単位の一次単体は元の代表辺。
方針：coslice 成分の回収と辺の coslice 表示の往復を使う。
規約：端点の正規化以外に単位を変更しない。
使われ方：指定単位の写像空間条件を持ち上げる。 -/
lemma rightUnitVertex_edge {C D : PresentableInfinityObject.{u}}
    {w : PrRFunctorSpace D C _⦋0⦌} {L : C.obj ⟶ D.obj}
    (a : QCatAdjunction L (rightVertexFunctor w)) :
    (rightUnitEdge (rightUnitVertex a)).edge =
      (functorEdgeOfSimplicialHomotopy (functorHomHomotopy a.unitHom)).edge := by
  exact (congrArg (fun s ↦ (sliceUnderVertexEdge (functorVertex (𝟙 C.obj)) s).edge)
    (rightUnitVertex_slice a)).trans (unitCosliceEdge_roundtrip _)

/-- 概要：指定随伴の持ち上げは元の単位の随伴条件を満たす。
方針：同じ代表辺の Hom 類を回収し、元の単位条件を端点の等式で移す。
規約：元の指定単位を保ち、任意の随伴単位を選び直さない。
使われ方：随伴単位の全部分空間の基準頂点。 -/
lemma rightUnitVertex_condition {C D : PresentableInfinityObject.{u}}
    {w : PrRFunctorSpace D C _⦋0⦌} {L : C.obj ⟶ D.obj}
    (a : QCatAdjunction L (rightVertexFunctor w)) :
    UnitMappingSpaceCondition (F := rightUnitLeftFunctor (rightUnitVertex a))
      (G := rightVertexFunctor w) (rightUnitHom (rightUnitVertex a)) := by
  have he : HEq (rightUnitHom (rightUnitVertex a)) a.unitHom :=
    (edgeHom_heq (rightUnitEdge (rightUnitVertex a))
      (functorEdgeOfSimplicialHomotopy (functorHomHomotopy a.unitHom))
      (rightUnitVertex_edge a)).trans
      (heq_of_eq (functorHomHomotopy_hom a.unitHom))
  exact (unitCondition_transport (rightUnitVertex_left a) rfl
    (rightUnitHom (rightUnitVertex a)) a.unitHom he).mpr a.unitMappingSpaceCondition

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
