module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.UnitFiberComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.UnitCosliceTriangle

/-!
概要：固定右の coslice の実単位と左関手を元の関手圏で読む。
方針：引き戻しの二射影で端点を正規化し、coslice の三角形を保持する。
規約：元の一次単体と二単体を変更しない。
使われ方：普遍単位と元の随伴単位の条件の比較。

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

/-- 概要：固定右の実単位の左関手を取り出す。
方針：底の関手頂点を元の単体集合の射へ戻す。
規約：左関手の保存条件はまだ要求しない。
使われ方：指定単位による随伴性の判定。 -/
def rightUnitLeftFunctor {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    {w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌} (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RightUnitCoslice C D w _⦋0⦌) : C.obj ⟶ D.obj :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C.obj D.obj).symm
    ((pullback.snd _ ((ihom C.obj).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w))).app (Opposite.op ⦋0⦌) v)

/-- 概要：左関手を頂点に戻すと元の底の頂点。
方針：関手頂点の表示の両逆を使う。
規約：頂点の厳密な等式。
使われ方：単位と比較辺の端点を正規化する。 -/
lemma rightUnitLeftFunctor_vertex {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    {w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌} (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RightUnitCoslice C D w _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (rightUnitLeftFunctor v) =
      (pullback.snd _ ((ihom C.obj).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w))).app (Opposite.op ⦋0⦌) v :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C.obj D.obj).apply_symm_apply _

/-- 概要：固定右の coslice の単位を元の id→LR の辺に戻す。
方針：coslice の辺の終点を引き戻しの可換性で同定する。
規約：元の単位の一次単体を保持する。
使われ方：全関手圏における単位条件。 -/
def rightUnitEdge {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    {w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌} (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RightUnitCoslice C D w _⦋0⦌) :
    SSet.Truncated.Edge (X := (truncation 2).obj ((ihom C.obj).obj C.obj))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (rightUnitLeftFunctor v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w)) where
  edge := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj))
    ((pullback.fst _ ((ihom C.obj).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w))).app (Opposite.op ⦋0⦌) v)).edge
  src_eq := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj))
    ((pullback.fst _ ((ihom C.obj).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w))).app (Opposite.op ⦋0⦌) v)).src_eq
  tgt_eq := by
    rw [(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj))
      ((pullback.fst _ ((ihom C.obj).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w))).app (Opposite.op ⦋0⦌) v)).tgt_eq]
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (pullback.condition (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection
        (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj))))) (Opposite.op ⦋0⦌)) v
    refine h.trans ?_
    exact congrArg (fun z ↦ ((ihom C.obj).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w)).app
      (Opposite.op ⦋0⦌) z) (rightUnitLeftFunctor_vertex v).symm

/-- 概要：固定右の実単位の元の h Fun の表示。
方針：正規化した辺の類を取る。
規約：coslice には実単位の高次単体を残す。
使われ方：元の随伴の指定単位の判定。 -/
def rightUnitHom {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    {w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌} (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RightUnitCoslice C D w _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 C.obj) (rightUnitLeftFunctor v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w) :=
  SSet.Truncated.HomotopyCategory.homMk (rightUnitEdge v)

/-- 概要：固定右 coslice の辺が与える左関手の間の比較辺。
方針：底の第二射影に写し、両端を元の関手頂点に正規化する。
規約：元の比較の一次単体を保持する。
使われ方：単位条件を移送する左関手の同型。 -/
def rightUnitLeftEdge {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    {w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌} {v v' : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RightUnitCoslice C D w _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RightUnitCoslice C D w)) v v') :
    SSet.Truncated.Edge (X := (truncation 2).obj ((ihom C.obj).obj D.obj))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (rightUnitLeftFunctor v)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (rightUnitLeftFunctor v')) where
  edge := (pullback.snd _ ((ihom C.obj).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w))).app (Opposite.op ⦋1⦌) e.edge
  src_eq := (e.map ((truncation 2).map (pullback.snd _
    ((ihom C.obj).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w))))).src_eq.trans (rightUnitLeftFunctor_vertex v).symm
  tgt_eq := (e.map ((truncation 2).map (pullback.snd _
    ((ihom C.obj).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w))))).tgt_eq.trans (rightUnitLeftFunctor_vertex v').symm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
