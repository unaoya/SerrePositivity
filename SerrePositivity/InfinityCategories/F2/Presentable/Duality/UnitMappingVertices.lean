module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.UnitMappingSpace
public import SerrePositivity.InfinityCategories.Core.InitialHomotopy
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyRepresentative

/-!
概要：元の全随伴を実単位の対応空間の頂点に持ち上げる。
方針：元の単位の代表辺を coslice と引き戻しに戻し、指定単位の判定を回収する。
規約：左右の元の関手圏の頂点を厳密に保持する。
使われ方：対応空間の両射影の頂点上の存在証明。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：二つの元の関手圏の頂点を core の積の頂点にする。
方針：core が全ての零単体を含むことを使う。
規約：元の関手頂点を変更しない。
使われ方：実単位の引き戻しの底の指定。 -/
def unitBaseVertex {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌) :
    (PrLMappingSpace C D ⊗ PrRMappingSpace D C) _⦋0⦌ :=
  (⟨v, quasicategoryCore_vertex v⟩, ⟨w, quasicategoryCore_vertex w⟩)

/-- 概要：指定された左右の関手に対する実単位の辺の型。
方針：恒等関手から元の LR への関手圏の辺を使う。
規約：随伴性は型に含めない。
使われ方：実単位の頂点の構成と回収の型。 -/
abbrev UnitMappingEdge {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌) :=
  SSet.Truncated.Edge (X := (truncation 2).obj ((ihom C.obj).obj C.obj))
    (functorVertex (𝟙 C.obj)) (functorVertex (leftVertexFunctor v ≫ rightVertexFunctor w))

/-- 概要：元の実単位の辺を対応の母空間の頂点にする。
方針：同じ辺を coslice 頂点にし、同じ左右の頂点とともに引き戻す。
規約：随伴性はここでは要求しない。
使われ方：指定された随伴の単位の持ち上げ。 -/
def rawUnitVertex {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom C.obj).obj C.obj))
      (functorVertex (𝟙 C.obj)) (functorVertex (leftVertexFunctor v ≫ rightVertexFunctor w))) :
    RawAdjointUnitSpace C D _⦋0⦌ :=
  SSet.yonedaEquiv (pullback.lift (SSet.yonedaEquiv.symm (edgeCosliceVertex e))
    (SSet.yonedaEquiv.symm (unitBaseVertex v w)) (by
      rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp,
        edgeCosliceVertex_projection, unitBaseVertex, unitComposition_vertex]))

/-- 概要：実単位頂点の coslice 成分を回収する。
方針：引き戻しの第一脚の計算則。
規約：元の辺の coslice 頂点を厳密に回収する。
使われ方：単位の一次単体の照合。 -/
lemma rawUnitVertex_slice {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (e : UnitMappingEdge v w) :
    (pullback.fst _ (unitComposition C D)).app (Opposite.op ⦋0⦌)
      (rawUnitVertex v w e) = edgeCosliceVertex e := by
  dsimp only [rawUnitVertex, RawAdjointUnitSpace]
  rw [← SSet.yonedaEquiv_comp, pullback.lift_fst, Equiv.apply_symm_apply]

/-- 概要：実単位頂点の左右の関手を回収する。
方針：引き戻しの第二脚の計算則。
規約：元の core の積の頂点を厳密に回収する。
使われ方：両射影の頂点上の計算。 -/
lemma rawUnitVertex_base {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (e : UnitMappingEdge v w) :
    (pullback.snd _ (unitComposition C D)).app (Opposite.op ⦋0⦌)
      (rawUnitVertex v w e) = unitBaseVertex v w := by
  dsimp only [rawUnitVertex, RawAdjointUnitSpace]
  rw [← SSet.yonedaEquiv_comp, pullback.lift_snd, Equiv.apply_symm_apply]

/-- 概要：実単位の持ち上げの左関手は元の左関手。
方針：底の頂点の第一成分を回収する。
規約：関手そのものの等式。
使われ方：単位の判定の始域の同定。 -/
lemma rawUnitVertex_left {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (e : UnitMappingEdge v w) :
    unitLeftFunctor (rawUnitVertex v w e) = leftVertexFunctor v := by
  simp only [unitLeftFunctor, rawUnitVertex_base, unitBaseVertex]

/-- 概要：実単位の持ち上げの右関手は元の右関手。
方針：底の頂点の第二成分を回収する。
規約：関手そのものの等式。
使われ方：単位の判定の終域の同定。 -/
lemma rawUnitVertex_right {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (e : UnitMappingEdge v w) :
    unitRightFunctor (rawUnitVertex v w e) = rightVertexFunctor w := by
  simp only [unitRightFunctor, rawUnitVertex_base, unitBaseVertex]

/-- 概要：辺を coslice 頂点にして戻すと同じ一次単体を得る。
方針：二点の join と標準辺の同型の両逆を計算する。
規約：端点を正規化した coslice の辺の表示を使う。
使われ方：実単位の回収の一般計算。 -/
lemma unitCosliceEdge_roundtrip {X : SSet.{u + 1}} {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    (sliceUnderVertexEdge x (edgeCosliceVertex e)).edge = e.edge := by
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
    ((joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm e.edge)) = e.edge
  rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

/-- 概要：持ち上げから回収する単位の一次単体は元の単体。
方針：coslice と標準辺の同型の両逆を計算する。
規約：端点の証拠の選択に依存しない。
使われ方：元の単位の h Fun の表示の回収。 -/
lemma rawUnitVertex_edge {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (e : UnitMappingEdge v w) :
    (unitCorrespondenceEdge (rawUnitVertex v w e)).edge = e.edge := by
  have h := congrArg (fun s ↦
    (sliceUnderVertexEdge (functorVertex (𝟙 C.obj)) s).edge)
    (rawUnitVertex_slice v w e)
  exact h.trans (unitCosliceEdge_roundtrip e)

/-- 概要：同じ一次単体の辺の類は端点の輸送込みで一致する。
方針：端点を面の等式で同定し、辺の外延性を使う。
規約：異種等式で端点の証拠への依存を除く。
使われ方：実単位の回収の検証。 -/
lemma edgeHom_heq {X : SSet.{u + 1}} {x y x' y' : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (e' : SSet.Truncated.Edge (X := (truncation 2).obj X) x' y') (h : e.edge = e'.edge) :
    HEq (SSet.Truncated.HomotopyCategory.homMk e)
      (SSet.Truncated.HomotopyCategory.homMk e') := by
  have hx : x = x' := e.src_eq.symm.trans ((congrArg (X.δ 1) h).trans e'.src_eq)
  have hy : y = y' := e.tgt_eq.symm.trans ((congrArg (X.δ 0) h).trans e'.tgt_eq)
  subst x' y'
  have he : e = e' := SSet.Truncated.Edge.ext h
  subst e'
  rfl

/-- 概要：単位の随伴判定は同じ関手・単位の輸送で保存される。
方針：関手の等式と単位の異種等式を消去する。
規約：随伴性の追加仮定を導入しない。
使われ方：元の随伴の単位判定を対応空間へ移す。 -/
lemma unitCondition_transport {C D : SSet.{u + 1}}
    [Quasicategory C] [Quasicategory D] {L L' : C ⟶ D} {R R' : D ⟶ C}
    (hL : L = L') (hR : R = R')
    (η : FunctorHom (𝟙 C) (L ≫ R)) (η' : FunctorHom (𝟙 C) (L' ≫ R'))
    (hη : HEq η η') : UnitMappingSpaceCondition η ↔ UnitMappingSpaceCondition η' := by
  subst L' R'
  cases hη
  rfl

/-- 概要：指定した元の全随伴を実単位の対応空間へ持ち上げる。
方針：同じ単位の代表を選び、元の随伴の単位条件を母空間の頂点へ移す。
規約：存在を仮定するのは指定されたこの随伴の証拠だけ。
使われ方：d の随伴を両射影の存在証明へ接続する。 -/
def adjointUnitVertex {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (a : QCatAdjunction (leftVertexFunctor v) (rightVertexFunctor w)) :
    AdjointUnitMappingSpace C D _⦋0⦌ := by
  let e := functorEdgeOfSimplicialHomotopy (functorHomHomotopy a.unitHom)
  let x := rawUnitVertex v w e
  have he : HEq (unitCorrespondenceHom x) a.unitHom :=
    (edgeHom_heq (unitCorrespondenceEdge x) e (rawUnitVertex_edge v w e)).trans
      (heq_of_eq (functorHomHomotopy_hom a.unitHom))
  have hx : UnitMappingSpaceCondition (unitCorrespondenceHom x) :=
    (unitCondition_transport (rawUnitVertex_left v w e) (rawUnitVertex_right v w e)
      (unitCorrespondenceHom x) a.unitHom he).mpr a.unitMappingSpaceCondition
  let y : (fullSubcomplexOnVertices (RawAdjointUnitSpace C D)
      (fun z ↦ UnitMappingSpaceCondition (unitCorrespondenceHom z)) : SSet.{u + 1}) _⦋0⦌ :=
    ⟨x, by
      intro f
      have hf : f = 𝟙 _ := Subsingleton.elim _ _
      subst f
      rw [op_id, (RawAdjointUnitSpace C D).map_id]
      exact hx⟩
  exact ⟨y, quasicategoryCore_vertex y⟩

/-- 概要：随伴の単位頂点の左射影は元の左頂点。
方針：母空間の底の第一成分を計算する。
規約：core の元の頂点との厳密な等式。
使われ方：左射影の頂点上の全射性。 -/
lemma adjointUnitVertex_left {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (a : QCatAdjunction (leftVertexFunctor v) (rightVertexFunctor w)) :
    (adjointUnitLeft C D).app (Opposite.op ⦋0⦌) (adjointUnitVertex v w a) =
      ⟨v, quasicategoryCore_vertex v⟩ := by
  change ((pullback.snd _ (unitComposition C D)).app (Opposite.op ⦋0⦌)
    (rawUnitVertex v w (functorEdgeOfSimplicialHomotopy
      (functorHomHomotopy a.unitHom)))).1 = _
  rw [rawUnitVertex_base]
  rfl

/-- 概要：随伴の単位頂点の右射影は元の右頂点。
方針：母空間の底の第二成分を計算する。
規約：元の右写像空間の頂点を厳密に回収する。
使われ方：右射影の頂点上の全射性。 -/
lemma adjointUnitVertex_right {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (a : QCatAdjunction (leftVertexFunctor v) (rightVertexFunctor w)) :
    (adjointUnitRight C D).app (Opposite.op ⦋0⦌) (adjointUnitVertex v w a) =
      ⟨w, quasicategoryCore_vertex w⟩ := by
  change ((pullback.snd _ (unitComposition C D)).app (Opposite.op ⦋0⦌)
    (rawUnitVertex v w (functorEdgeOfSimplicialHomotopy
      (functorHomHomotopy a.unitHom)))).2 = _
  rw [rawUnitVertex_base]
  rfl

/-- 概要：実単位の対応の左射影は元の全ての左頂点を覆う。
方針：d の随伴関手定理で選んだ右随伴とその実単位を持ち上げる。
規約：同型への弱い一致ではなく頂点上の全射。
使われ方：写像空間の左射影の同値性の存在方向。 -/
lemma adjointUnitLeft_surjective (C D : PresentableInfinityObject.{u}) :
    Function.Surjective ((adjointUnitLeft C D).app (Opposite.op ⦋0⦌)) := by
  intro v
  have a : QCatAdjunction (leftVertexFunctor v.val)
      (rightVertexFunctor (rightAdjointVertex v.val)) := by
    simpa only [rightAdjointVertex, rightFunctorVertex, rightVertexFunctor,
      Equiv.symm_apply_apply] using chosenRightAdjunction v.val
  refine ⟨adjointUnitVertex v.val (rightAdjointVertex v.val) a, ?_⟩
  exact (adjointUnitVertex_left _ _ a).trans (Subtype.ext rfl)

/-- 概要：実単位の対応の右射影は元の全ての右頂点を覆う。
方針：d の随伴関手定理で選んだ左随伴とその実単位を持ち上げる。
規約：元の右関手圏の全頂点を保持する。
使われ方：写像空間の右射影の同値性の存在方向。 -/
lemma adjointUnitRight_surjective (C D : PresentableInfinityObject.{u}) :
    Function.Surjective ((adjointUnitRight C D).app (Opposite.op ⦋0⦌)) := by
  intro w
  have a : QCatAdjunction (leftVertexFunctor (leftAdjointVertex w.val))
      (rightVertexFunctor w.val) := by
    simpa only [leftAdjointVertex, leftFunctorVertex, leftVertexFunctor,
      Equiv.symm_apply_apply] using chosenLeftAdjunction w.val
  refine ⟨adjointUnitVertex (leftAdjointVertex w.val) w.val a, ?_⟩
  exact (adjointUnitVertex_right _ _ a).trans (Subtype.ext rfl)

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
