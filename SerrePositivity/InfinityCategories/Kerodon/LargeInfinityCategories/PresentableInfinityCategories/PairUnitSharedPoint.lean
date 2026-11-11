module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PairPointedRightRestrictionFibers

/-!
概要：左右の固定 coslice の元の指定単位は、同じ全二変数単位空間で同じ点になる。
方針：引き戻し同型の単位成分と底成分を計算し、同じ単位の辺と両関手を回収する。
規約：左右で指定点を別に選び直さない。
使われ方：相対評価と全左 Hom の輸送を同じ pointed 単位像で照合する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：固定左の全単位空間への包含は元の実単位の成分を保持する。
方針：二つの引き戻しの貼り合わせの第一脚を逆向きに計算する。
規約：元の単位辺を保持する。
使われ方：左右の指定単位の同一点性。 -/
lemma pairLeftUnitIntoJoint_unit {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairLeftUnitIntoJoint v ≫ pullback.fst
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj))))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairUnitComposition C D) =
      pullback.fst _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightFunctorInclusion D C) ≫ pullback.fst
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj))))
        ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor v)).app C.obj) := by
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairLeftUnitIntoJoint, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairFixedLeftCosliceIso, pullback.congrHom_inv,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantPairUnitProjection, Category.assoc]

/-- 概要：固定右の全単位空間への包含は元の実単位の成分を保持する。
方針：同じ貼り合わせ同型の逆の第一脚を計算する。
規約：元の単位辺を保持する。
使われ方：左右の同じ実単位の同定。 -/
lemma pairRightUnitIntoJoint_unit {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairRightUnitIntoJoint w ≫ pullback.fst
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj))))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairUnitComposition C D) =
      pullback.fst _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftFunctorInclusion C D) ≫ pullback.fst
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj))))
        ((ihom C.obj).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w)) := by
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairRightUnitIntoJoint, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairFixedRightCosliceIso, pullback.congrHom_inv,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantPairUnitProjection, Category.assoc]

/-- 概要：固定左の底は元の二つの関手の頂点の対。
方針：零次の定値単体を計算する。
規約：頂点の厳密な等式。
使われ方：全単位空間の底の同定。 -/
lemma pairFixedLeftBase_vertex {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairFixedLeftBase v).app (Opposite.op ⦋0⦌) w = (v, w) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 0, w) = (v, w)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]

/-- 概要：固定右の底は元の二つの関手の頂点の同じ対。
方針：零次の定値単体を計算する。
規約：左右で同じ頂点の順序を使う。
使われ方：同じ全単位空間の底の同定。 -/
lemma pairFixedRightBase_vertex {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairFixedRightBase w).app (Opposite.op ⦋0⦌) v = (v, w) := by
  change (v, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant w 0) = (v, w)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]

/-- 概要：元の随伴単位は左右の固定空間から同じ全単位空間の同じ点に移る。
方針：単位成分は同じ代表辺、底成分は同じ元の関手対であることを計算する。
規約：単位のホモトピー類だけでなく零単体を厳密に同定する。
使われ方：評価と輸送の指定点の一致。 -/
lemma pairUnitIntoJoint_vertex_eq {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor v) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairLeftUnitIntoJoint v).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservingLeftUnitVertex v w a) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairRightUnitIntoJoint w).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservingRightUnitVertex v w a) := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj)))
  let f := (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor v)).app C.obj
  let g := (ihom C.obj).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w)
  let l := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservingLeftUnitVertex v w a
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservingRightUnitVertex v w a
  have hL := congrArg (fun k : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservingLeftUnitCoslice v ⟶ _ ↦ k.app (Opposite.op ⦋0⦌) l)
    (pairLeftUnitIntoJoint_unit v)
  have hR := congrArg (fun k : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservingRightUnitCoslice w ⟶ _ ↦ k.app (Opposite.op ⦋0⦌) r)
    (pairRightUnitIntoJoint_unit w)
  have hLu : (pullback.fst p (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairUnitComposition C D)).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairLeftUnitIntoJoint v).app (Opposite.op ⦋0⦌) l) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.edgeCosliceVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy a.unitHom)) :=
    hL.trans ((congrArg ((pullback.fst p f).app (Opposite.op ⦋0⦌))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservingLeftUnitVertex_full v w a)).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftUnitVertex_slice a))
  have hRu : (pullback.fst p (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairUnitComposition C D)).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairRightUnitIntoJoint w).app (Opposite.op ⦋0⦌) r) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.edgeCosliceVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy a.unitHom)) :=
    hR.trans ((congrArg ((pullback.fst p g).app (Opposite.op ⦋0⦌))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservingRightUnitVertex_full v w a)).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightUnitVertex_slice a))
  have hLb := congrArg (fun k : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservingLeftUnitCoslice v ⟶ _ ↦ k.app (Opposite.op ⦋0⦌) l)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairLeftUnitIntoJoint_projection v)
  have hRb := congrArg (fun k : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservingRightUnitCoslice w ⟶ _ ↦ k.app (Opposite.op ⦋0⦌) r)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairRightUnitIntoJoint_projection w)
  have hLbase : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantPairUnitProjection C D).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairLeftUnitIntoJoint v).app (Opposite.op ⦋0⦌) l) = (v, w) :=
    hLb.trans ((congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairFixedLeftBase v).app (Opposite.op ⦋0⦌))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservingLeftUnitVertex_base v w a)).trans (pairFixedLeftBase_vertex v w))
  have hRbase : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantPairUnitProjection C D).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairRightUnitIntoJoint w).app (Opposite.op ⦋0⦌) r) = (v, w) :=
    hRb.trans ((congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairFixedRightBase w).app (Opposite.op ⦋0⦌))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservingRightUnitVertex_base v w a)).trans (pairFixedRightBase_vertex v w))
  apply SSet.yonedaEquiv.symm.injective
  apply pullback.hom_ext
  · exact (SSet.yonedaEquiv_symm_comp _ _).trans
      ((congrArg SSet.yonedaEquiv.symm (hLu.trans hRu.symm)).trans
        (SSet.yonedaEquiv_symm_comp _ _).symm)
  · exact (SSet.yonedaEquiv_symm_comp _ _).trans
      ((congrArg SSet.yonedaEquiv.symm (hLbase.trans hRbase.symm)).trans
        (SSet.yonedaEquiv_symm_comp _ _).symm)

/-- 概要：左右の元の単位の pointed-space への像は同じ指定点。
方針：同じ全単位空間での頂点の等式を一つの全体比較に通す。
規約：左右で点の像を選び直さない。
使われ方：実 Hom 作用後の評価と始単位からの輸送の一致。 -/
lemma pairUnitPointedDisplay_vertex_eq {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor v) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairLeftUnitPointedDisplay v).app (Opposite.op ⦋0⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservingLeftUnitVertex v w a)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairRightUnitPointedDisplay w).app (Opposite.op ⦋0⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservingRightUnitVertex v w a)) :=
  congrArg (fun x ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairUnitPointedDisplay C D).app (Opposite.op ⦋0⦌) (ULift.up x))
    (pairUnitIntoJoint_vertex_eq v w a)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
