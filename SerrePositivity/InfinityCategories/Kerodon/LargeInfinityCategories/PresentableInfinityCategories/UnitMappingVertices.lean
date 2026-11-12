module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.UnitMappingSpace
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialHomotopy
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative

/-!
概要：元の全随伴を実単位の対応空間の頂点に持ち上げる。
方針：元の単位の代表辺を coslice と引き戻しに戻し、指定単位の判定を回収する。
規約：左右の元の関手圏の頂点を厳密に保持する。
使われ方：対応空間の両射影の頂点上の存在証明。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：二つの元の関手圏の頂点を core の積の頂点にする。
方針：core が全ての零単体を含むことを使う。
規約：元の関手頂点を変更しない。
使われ方：実単位の引き戻しの底の指定。 -/
def unitBaseVertex {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLMappingSpace C D ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRMappingSpace D C) _⦋0⦌ :=
  (⟨v, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_vertex v⟩, ⟨w, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_vertex w⟩)

/-- 概要：指定された左右の関手に対する実単位の辺の型。
方針：恒等関手から元の LR への関手圏の辺を使う。
規約：随伴性は型に含めない。
使われ方：実単位の頂点の構成と回収の型。 -/
abbrev UnitMappingEdge {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌) :=
  SSet.Truncated.Edge (X := (truncation 2).obj ((ihom C.obj).obj C.obj))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w))

/-- 概要：元の実単位の辺を対応の母空間の頂点にする。
方針：同じ辺を coslice 頂点にし、同じ左右の頂点とともに引き戻す。
規約：随伴性はここでは要求しない。
使われ方：指定された随伴の単位の持ち上げ。 -/
def rawUnitVertex {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌)
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom C.obj).obj C.obj))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RawAdjointUnitSpace C D _⦋0⦌ :=
  SSet.yonedaEquiv (pullback.lift (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.edgeCosliceVertex e))
    (SSet.yonedaEquiv.symm (unitBaseVertex v w)) (by
      rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp,
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.edgeCosliceVertex_projection, unitBaseVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitComposition_vertex]))

/-- 概要：実単位頂点の coslice 成分を回収する。
方針：引き戻しの第一脚の計算則。
規約：元の辺の coslice 頂点を厳密に回収する。
使われ方：単位の一次単体の照合。 -/
lemma rawUnitVertex_slice {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌)
    (e : UnitMappingEdge v w) :
    (pullback.fst _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitComposition C D)).app (Opposite.op ⦋0⦌)
      (rawUnitVertex v w e) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.edgeCosliceVertex e := by
  dsimp only [rawUnitVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RawAdjointUnitSpace]
  rw [← SSet.yonedaEquiv_comp, pullback.lift_fst, Equiv.apply_symm_apply]

/-- 概要：実単位頂点の左右の関手を回収する。
方針：引き戻しの第二脚の計算則。
規約：元の core の積の頂点を厳密に回収する。
使われ方：両射影の頂点上の計算。 -/
lemma rawUnitVertex_base {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌)
    (e : UnitMappingEdge v w) :
    (pullback.snd _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitComposition C D)).app (Opposite.op ⦋0⦌)
      (rawUnitVertex v w e) = unitBaseVertex v w := by
  dsimp only [rawUnitVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RawAdjointUnitSpace]
  rw [← SSet.yonedaEquiv_comp, pullback.lift_snd, Equiv.apply_symm_apply]

/-- 概要：実単位の持ち上げの左関手は元の左関手。
方針：底の頂点の第一成分を回収する。
規約：関手そのものの等式。
使われ方：単位の判定の始域の同定。 -/
lemma rawUnitVertex_left {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌)
    (e : UnitMappingEdge v w) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitLeftFunctor (rawUnitVertex v w e) = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor v := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitLeftFunctor, rawUnitVertex_base, unitBaseVertex]

/-- 概要：実単位の持ち上げの右関手は元の右関手。
方針：底の頂点の第二成分を回収する。
規約：関手そのものの等式。
使われ方：単位の判定の終域の同定。 -/
lemma rawUnitVertex_right {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌)
    (e : UnitMappingEdge v w) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitRightFunctor (rawUnitVertex v w e) = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitRightFunctor, rawUnitVertex_base, unitBaseVertex]

/-- 概要：辺を coslice 頂点にして戻すと同じ一次単体を得る。
方針：二点の join と標準辺の同型の両逆を計算する。
規約：端点を正規化した coslice の辺の表示を使う。
使われ方：実単位の回収の一般計算。 -/
lemma unitCosliceEdge_roundtrip {X : SSet.{u + 1}} {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderVertexEdge x (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.edgeCosliceVertex e)).edge = e.edge := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm e.edge)) = e.edge
  rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

/-- 概要：持ち上げから回収する単位の一次単体は元の単体。
方針：coslice と標準辺の同型の両逆を計算する。
規約：端点の証拠の選択に依存しない。
使われ方：元の単位の h Fun の表示の回収。 -/
lemma rawUnitVertex_edge {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌)
    (e : UnitMappingEdge v w) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCorrespondenceEdge (rawUnitVertex v w e)).edge = e.edge := by
  have h := congrArg (fun s ↦
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj)) s).edge)
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
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 C) (L ≫ R)) (η' : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 C) (L' ≫ R'))
    (hη : HEq η η') : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition η ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition η' := by
  subst L' R'
  cases hη
  rfl

/-- 概要：指定した元の全随伴を実単位の対応空間へ持ち上げる。
方針：同じ単位の代表を選び、元の随伴の単位条件を母空間の頂点へ移す。
規約：存在を仮定するのは指定されたこの随伴の証拠だけ。
使われ方：d の随伴を両射影の存在証明へ接続する。 -/
def adjointUnitVertex {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor v) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AdjointUnitMappingSpace C D _⦋0⦌ := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy a.unitHom)
  let x := rawUnitVertex v w e
  have he : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCorrespondenceHom x) a.unitHom :=
    (edgeHom_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCorrespondenceEdge x) e (rawUnitVertex_edge v w e)).trans
      (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom a.unitHom))
  have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCorrespondenceHom x) :=
    (unitCondition_transport (rawUnitVertex_left v w e) (rawUnitVertex_right v w e)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCorrespondenceHom x) a.unitHom he).mpr a.unitMappingSpaceCondition
  let y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RawAdjointUnitSpace C D)
      (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCorrespondenceHom z)) : SSet.{u + 1}) _⦋0⦌ :=
    ⟨x, by
      intro f
      have hf : f = 𝟙 _ := Subsingleton.elim _ _
      subst f
      rw [op_id, (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RawAdjointUnitSpace C D).map_id]
      exact hx⟩
  exact ⟨y, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_vertex y⟩

/-- 概要：随伴の単位頂点の左射影は元の左頂点。
方針：母空間の底の第一成分を計算する。
規約：core の元の頂点との厳密な等式。
使われ方：左射影の頂点上の全射性。 -/
lemma adjointUnitVertex_left {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor v) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointUnitLeft C D).app (Opposite.op ⦋0⦌) (adjointUnitVertex v w a) =
      ⟨v, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_vertex v⟩ := by
  change ((pullback.snd _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitComposition C D)).app (Opposite.op ⦋0⦌)
    (rawUnitVertex v w (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy a.unitHom)))).1 = _
  rw [rawUnitVertex_base]
  rfl

/-- 概要：随伴の単位頂点の右射影は元の右頂点。
方針：母空間の底の第二成分を計算する。
規約：元の右写像空間の頂点を厳密に回収する。
使われ方：右射影の頂点上の全射性。 -/
lemma adjointUnitVertex_right {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor v) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointUnitRight C D).app (Opposite.op ⦋0⦌) (adjointUnitVertex v w a) =
      ⟨w, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_vertex w⟩ := by
  change ((pullback.snd _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitComposition C D)).app (Opposite.op ⦋0⦌)
    (rawUnitVertex v w (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy a.unitHom)))).2 = _
  rw [rawUnitVertex_base]
  rfl

/-- 概要：実単位の対応の左射影は元の全ての左頂点を覆う。
方針：d の随伴関手定理で選んだ右随伴とその実単位を持ち上げる。
規約：同型への弱い一致ではなく頂点上の全射。
使われ方：写像空間の左射影の同値性の存在方向。 -/
lemma adjointUnitLeft_surjective (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointUnitLeft C D).app (Opposite.op ⦋0⦌)) := by
  intro v
  have a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor v.val)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjointVertex v.val)) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjointVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightFunctorVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor,
      Equiv.symm_apply_apply] using _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenRightAdjunction v.val
  refine ⟨adjointUnitVertex v.val (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjointVertex v.val) a, ?_⟩
  exact (adjointUnitVertex_left _ _ a).trans (Subtype.ext rfl)

/-- 概要：実単位の対応の右射影は元の全ての右頂点を覆う。
方針：d の随伴関手定理で選んだ左随伴とその実単位を持ち上げる。
規約：元の右関手圏の全頂点を保持する。
使われ方：写像空間の右射影の同値性の存在方向。 -/
lemma adjointUnitRight_surjective (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointUnitRight C D).app (Opposite.op ⦋0⦌)) := by
  intro w
  have a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftAdjointVertex w.val))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w.val) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftAdjointVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftFunctorVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor,
      Equiv.symm_apply_apply] using _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenLeftAdjunction w.val
  refine ⟨adjointUnitVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftAdjointVertex w.val) w.val a, ?_⟩
  exact (adjointUnitVertex_right _ _ a).trans (Subtype.ext rfl)

/-- 概要：実単位の対応の左射影は本質的全射。
方針：頂点上の全射性を恒等同型と組み合わせる。
規約：元の e1 の写像空間への射についての主張。
使われ方：左射影の QCat 同値判定の存在側。 -/
lemma adjointUnitLeft_isEssentiallySurjective (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointUnitLeft C D) := by
  intro v
  obtain ⟨x, rfl⟩ := adjointUnitLeft_surjective C D v
  exact ⟨x, ⟨Iso.refl _⟩⟩

/-- 概要：実単位の対応の右射影は本質的全射。
方針：頂点上の全射性を恒等同型と組み合わせる。
規約：元の e1 の逆向きの写像空間への射についての主張。
使われ方：右射影の QCat 同値判定の存在側。 -/
lemma adjointUnitRight_isEssentiallySurjective (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointUnitRight C D) := by
  intro w
  obtain ⟨x, rfl⟩ := adjointUnitRight_surjective C D w
  exact ⟨x, ⟨Iso.refl _⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
