module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.PairAdjointCondition
public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.TwistedPairVertexConstruction

/-!
概要：元の随伴単位を全関手族の対応の頂点に戻す。
方針：実単位の辺を coslice 頂点とし、twisted 零単体の構成で両射影を固定する。
規約：元の左右の関手と元の単位の表示を使う。
使われ方：対ごとの両射影の頂点上の全射性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：元の左右の関手と実単位の辺を全関手族の母対応の頂点にする。
方針：同じ coslice 頂点を twisted 零単体に定値に持ち上げる。
規約：元の辺を保持し、随伴条件はまだ課さない。
使われ方：元の随伴から対応の頂点への持ち上げ。 -/
def pairRawUnitVertex {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (e : UnitMappingEdge v w) : PairRawUnitCorrespondence C D _⦋0⦌ :=
  twistedPairLiftVertex _ _ v (SSet.opObjEquiv.symm w) (edgeCosliceVertex e) (by
    rw [edgeCosliceVertex_projection, pairUnitComposition_vertex, Equiv.apply_symm_apply])

/-- 概要：元の単位から作った母対応頂点の左射影は指定した左頂点。
方針：twisted 零単体の構成の左回収公式を使う。
規約：元の全関手圏での頂点の等式。
使われ方：左射影の全射性。 -/
lemma pairRawUnitVertex_left {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (e : UnitMappingEdge v w) :
    (pairRawUnitLeft C D).app (Opposite.op ⦋0⦌) (pairRawUnitVertex v w e) = v :=
  twistedPairLiftVertex_left _ _ _ _ _ _

/-- 概要：元の単位から作った母対応頂点の右射影は指定した右頂点。
方針：twisted 零単体の右回収公式を使う。
規約：元の反対関手圏での頂点の等式。
使われ方：右射影の全射性。 -/
lemma pairRawUnitVertex_right {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (e : UnitMappingEdge v w) :
    (pairRawUnitRight C D).app (Opposite.op ⦋0⦌) (pairRawUnitVertex v w e) =
      SSet.opObjEquiv.symm w :=
  twistedPairLiftVertex_right _ _ _ _ _ _

/-- 概要：母対応頂点の元の左関手は指定した左関手。
方針：左射影の零単体の回収を関手頂点の逆に通す。
規約：元の関手の厳密な等式。
使われ方：指定単位の随伴条件の輸送。 -/
lemma pairRawUnitVertex_leftFunctor {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (e : UnitMappingEdge v w) :
    pairLeftFunctor (pairRawUnitVertex v w e) = leftVertexFunctor v := by
  unfold pairLeftFunctor
  rw [pairRawUnitVertex_left]

/-- 概要：母対応頂点の元の右関手は指定した右関手。
方針：右射影の回収の後に反転と関手頂点を戻す。
規約：元の関手の厳密な等式。
使われ方：指定単位の随伴条件の輸送。 -/
lemma pairRawUnitVertex_rightFunctor {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (e : UnitMappingEdge v w) :
    pairRightFunctor (pairRawUnitVertex v w e) = rightVertexFunctor w := by
  unfold pairRightFunctor
  rw [pairRawUnitVertex_right, Equiv.apply_symm_apply]

/-- 概要：母対応頂点が保持する単位の辺は元の実際の辺。
方針：定値単位の回収と coslice 頂点の往復を計算する。
規約：辺のホモトピー類だけでなく元の辺を回収する。
使われ方：指定単位条件の回収。 -/
lemma pairRawUnitVertex_edge {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (e : UnitMappingEdge v w) : (pairUnitEdge (pairRawUnitVertex v w e)).edge = e.edge := by
  change (sliceUnderVertexEdge (functorVertex (𝟙 C.obj))
    (twistedPairUnitVertex (pairRawUnitVertex v w e))).edge = e.edge
  rw [show twistedPairUnitVertex (pairRawUnitVertex v w e) = edgeCosliceVertex e from
    twistedPairLiftVertex_unit _ _ _ _ _ _]
  exact unitCosliceEdge_roundtrip _

/-- 概要：元の随伴を全関手族の随伴対応の頂点にする。
方針：元の単位の代表辺を持ち上げ、指定単位の条件を厳密な端点等式で輸送する。
規約：随伴条件の全部分複体を取り、core は取らない。
使われ方：両射影の本質的全射性の入力。 -/
def pairAdjointVertex {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (a : QCatAdjunction (leftVertexFunctor v) (rightVertexFunctor w)) :
    PairAdjointCorrespondence C D _⦋0⦌ := by
  let e := functorEdgeOfSimplicialHomotopy (functorHomHomotopy a.unitHom)
  let x := pairRawUnitVertex v w e
  have he : HEq (pairUnitHom x) a.unitHom :=
    (edgeHom_heq (pairUnitEdge x) e (pairRawUnitVertex_edge v w e)).trans
      (heq_of_eq (functorHomHomotopy_hom a.unitHom))
  have hx : UnitMappingSpaceCondition (F := pairLeftFunctor x)
      (G := pairRightFunctor x) (pairUnitHom x) :=
    (unitCondition_transport (pairRawUnitVertex_leftFunctor v w e)
      (pairRawUnitVertex_rightFunctor v w e) (pairUnitHom x) a.unitHom he).mpr
        a.unitMappingSpaceCondition
  refine ⟨x, ?_⟩
  intro f
  have hf : f = 𝟙 _ := Subsingleton.elim _ _
  subst f
  rw [op_id, (PairRawUnitCorrespondence C D).map_id]
  exact hx

/-- 概要：指定随伴からの対応頂点の左射影は元の左頂点。
方針：母対応の左回収公式を適用する。
規約：元の全関手圏の頂点の等式。
使われ方：左射影の本質的全射性。 -/
lemma pairAdjointVertex_left {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (a : QCatAdjunction (leftVertexFunctor v) (rightVertexFunctor w)) :
    (pairAdjointLeft C D).app (Opposite.op ⦋0⦌) (pairAdjointVertex v w a) = v :=
  pairRawUnitVertex_left _ _ _

/-- 概要：指定随伴からの対応頂点の右射影は元の右頂点。
方針：母対応の右回収公式を適用する。
規約：反対関手圏の元の頂点を保持する。
使われ方：右射影の本質的全射性。 -/
lemma pairAdjointVertex_right {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (a : QCatAdjunction (leftVertexFunctor v) (rightVertexFunctor w)) :
    (pairAdjointRight C D).app (Opposite.op ⦋0⦌) (pairAdjointVertex v w a) =
      SSet.opObjEquiv.symm w :=
  pairRawUnitVertex_right _ _ _

/-- 概要：全関手族の随伴対応の左射影は全ての元の左頂点を覆う。
方針：d の随伴関手定理で得た右随伴と指定単位を持ち上げる。
規約：充填性や同値性を頂点全射性で代用しない。
使われ方：対ごとの左射影の存在方向。 -/
lemma pairAdjointLeft_surjective (C D : PresentableInfinityObject.{u}) :
    Function.Surjective ((pairAdjointLeft C D).app (Opposite.op ⦋0⦌)) := by
  intro v
  have a : QCatAdjunction (leftVertexFunctor v)
      (rightVertexFunctor (rightAdjointVertex v)) := by
    simpa only [rightAdjointVertex, rightFunctorVertex, rightVertexFunctor,
      Equiv.symm_apply_apply] using chosenRightAdjunction v
  exact ⟨pairAdjointVertex v (rightAdjointVertex v) a, pairAdjointVertex_left _ _ a⟩

/-- 概要：全関手族の随伴対応の右射影は全ての元の右頂点を覆う。
方針：反転を解除した元の右関手の左随伴を d から持ち上げる。
規約：全右関手圏の反対の頂点についての全射。
使われ方：対ごとの右射影の存在方向。 -/
lemma pairAdjointRight_surjective (C D : PresentableInfinityObject.{u}) :
    Function.Surjective ((pairAdjointRight C D).app (Opposite.op ⦋0⦌)) := by
  intro w
  let w' : PrRFunctorSpace D C _⦋0⦌ := SSet.opObjEquiv w
  have a : QCatAdjunction (leftVertexFunctor (leftAdjointVertex w'))
      (rightVertexFunctor w') := by
    simpa only [leftAdjointVertex, leftFunctorVertex, leftVertexFunctor,
      Equiv.symm_apply_apply] using chosenLeftAdjunction w'
  refine ⟨pairAdjointVertex (leftAdjointVertex w') w' a, ?_⟩
  exact (pairAdjointVertex_right _ _ a).trans (SSet.opObjEquiv.symm_apply_apply w)

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
