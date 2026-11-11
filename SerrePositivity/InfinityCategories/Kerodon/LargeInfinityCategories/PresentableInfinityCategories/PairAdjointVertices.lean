module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PairAdjointCondition
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TwistedPairVertexConstruction

/-!
概要：元の随伴単位を全関手族の対応の頂点に戻す。
方針：実単位の辺を coslice 頂点とし、twisted 零単体の構成で両射影を固定する。
規約：元の左右の関手と元の単位の表示を使う。
使われ方：対ごとの両射影の頂点上の全射性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の左右の関手と実単位の辺を全関手族の母対応の頂点にする。
方針：同じ coslice 頂点を twisted 零単体に定値に持ち上げる。
規約：元の辺を保持し、随伴条件はまだ課さない。
使われ方：元の随伴から対応の頂点への持ち上げ。 -/
def pairRawUnitVertex {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.UnitMappingEdge v w) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PairRawUnitCorrespondence C D _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedPairLiftVertex _ _ v (SSet.opObjEquiv.symm w) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.edgeCosliceVertex e) (by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.edgeCosliceVertex_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairUnitComposition_vertex, Equiv.apply_symm_apply])

/-- 概要：元の単位から作った母対応頂点の左射影は指定した左頂点。
方針：twisted 零単体の構成の左回収公式を使う。
規約：元の全関手圏での頂点の等式。
使われ方：左射影の全射性。 -/
lemma pairRawUnitVertex_left {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.UnitMappingEdge v w) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairRawUnitLeft C D).app (Opposite.op ⦋0⦌) (pairRawUnitVertex v w e) = v :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedPairLiftVertex_left _ _ _ _ _ _

/-- 概要：元の単位から作った母対応頂点の右射影は指定した右頂点。
方針：twisted 零単体の右回収公式を使う。
規約：元の反対関手圏での頂点の等式。
使われ方：右射影の全射性。 -/
lemma pairRawUnitVertex_right {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.UnitMappingEdge v w) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairRawUnitRight C D).app (Opposite.op ⦋0⦌) (pairRawUnitVertex v w e) =
      SSet.opObjEquiv.symm w :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedPairLiftVertex_right _ _ _ _ _ _

/-- 概要：母対応頂点の元の左関手は指定した左関手。
方針：左射影の零単体の回収を関手頂点の逆に通す。
規約：元の関手の厳密な等式。
使われ方：指定単位の随伴条件の輸送。 -/
lemma pairRawUnitVertex_leftFunctor {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.UnitMappingEdge v w) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairLeftFunctor (pairRawUnitVertex v w e) = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor v := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairLeftFunctor
  rw [pairRawUnitVertex_left]

/-- 概要：母対応頂点の元の右関手は指定した右関手。
方針：右射影の回収の後に反転と関手頂点を戻す。
規約：元の関手の厳密な等式。
使われ方：指定単位の随伴条件の輸送。 -/
lemma pairRawUnitVertex_rightFunctor {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.UnitMappingEdge v w) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairRightFunctor (pairRawUnitVertex v w e) = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairRightFunctor
  rw [pairRawUnitVertex_right, Equiv.apply_symm_apply]

/-- 概要：母対応頂点が保持する単位の辺は元の実際の辺。
方針：定値単位の回収と coslice 頂点の往復を計算する。
規約：辺のホモトピー類だけでなく元の辺を回収する。
使われ方：指定単位条件の回収。 -/
lemma pairRawUnitVertex_edge {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.UnitMappingEdge v w) : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairUnitEdge (pairRawUnitVertex v w e)).edge = e.edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedPairUnitVertex (pairRawUnitVertex v w e))).edge = e.edge
  rw [show _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedPairUnitVertex (pairRawUnitVertex v w e) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.edgeCosliceVertex e from
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedPairLiftVertex_unit _ _ _ _ _ _]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCosliceEdge_roundtrip _

/-- 概要：元の随伴を全関手族の随伴対応の頂点にする。
方針：元の単位の代表辺を持ち上げ、指定単位の条件を厳密な端点等式で輸送する。
規約：随伴条件の全部分複体を取り、core は取らない。
使われ方：両射影の本質的全射性の入力。 -/
def pairAdjointVertex {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor v) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PairAdjointCorrespondence C D _⦋0⦌ := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy a.unitHom)
  let x := pairRawUnitVertex v w e
  have he : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairUnitHom x) a.unitHom :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.edgeHom_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairUnitEdge x) e (pairRawUnitVertex_edge v w e)).trans
      (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom a.unitHom))
  have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition (F := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairLeftFunctor x)
      (G := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairRightFunctor x) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairUnitHom x) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCondition_transport (pairRawUnitVertex_leftFunctor v w e)
      (pairRawUnitVertex_rightFunctor v w e) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairUnitHom x) a.unitHom he).mpr
        a.unitMappingSpaceCondition
  refine ⟨x, ?_⟩
  intro f
  have hf : f = 𝟙 _ := Subsingleton.elim _ _
  subst f
  rw [op_id, (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PairRawUnitCorrespondence C D).map_id]
  exact hx

/-- 概要：指定随伴からの対応頂点の左射影は元の左頂点。
方針：母対応の左回収公式を適用する。
規約：元の全関手圏の頂点の等式。
使われ方：左射影の本質的全射性。 -/
lemma pairAdjointVertex_left {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor v) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairAdjointLeft C D).app (Opposite.op ⦋0⦌) (pairAdjointVertex v w a) = v :=
  pairRawUnitVertex_left _ _ _

/-- 概要：指定随伴からの対応頂点の右射影は元の右頂点。
方針：母対応の右回収公式を適用する。
規約：反対関手圏の元の頂点を保持する。
使われ方：右射影の本質的全射性。 -/
lemma pairAdjointVertex_right {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor v) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairAdjointRight C D).app (Opposite.op ⦋0⦌) (pairAdjointVertex v w a) =
      SSet.opObjEquiv.symm w :=
  pairRawUnitVertex_right _ _ _

/-- 概要：全関手族の随伴対応の左射影は全ての元の左頂点を覆う。
方針：d の随伴関手定理で得た右随伴と指定単位を持ち上げる。
規約：充填性や同値性を頂点全射性で代用しない。
使われ方：対ごとの左射影の存在方向。 -/
lemma pairAdjointLeft_surjective (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairAdjointLeft C D).app (Opposite.op ⦋0⦌)) := by
  intro v
  have a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor v)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjointVertex v)) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjointVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightFunctorVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor,
      Equiv.symm_apply_apply] using _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenRightAdjunction v
  exact ⟨pairAdjointVertex v (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjointVertex v) a, pairAdjointVertex_left _ _ a⟩

/-- 概要：全関手族の随伴対応の右射影は全ての元の右頂点を覆う。
方針：反転を解除した元の右関手の左随伴を d から持ち上げる。
規約：全右関手圏の反対の頂点についての全射。
使われ方：対ごとの右射影の存在方向。 -/
lemma pairAdjointRight_surjective (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairAdjointRight C D).app (Opposite.op ⦋0⦌)) := by
  intro w
  let w' : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌ := SSet.opObjEquiv w
  have a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftAdjointVertex w'))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w') := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftAdjointVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftFunctorVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor,
      Equiv.symm_apply_apply] using _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenLeftAdjunction w'
  refine ⟨pairAdjointVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftAdjointVertex w') w' a, ?_⟩
  exact (pairAdjointVertex_right _ _ a).trans (SSet.opObjEquiv.symm_apply_apply w)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
