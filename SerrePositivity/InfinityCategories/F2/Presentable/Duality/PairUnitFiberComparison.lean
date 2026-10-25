module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.PairPreservingUnitVertices
public import SerrePositivity.InfinityCategories.Core.VertexFiberPullback

/-!
概要：左右の固定単位 coslice の同じ二関手上の fiber を、元の同じ実単位空間へ比較する。
方針：引き戻しの頂点 fiber の厳密な同型を二度使い、合成の頂点を正規化する。
規約：元の単位の全高次データを保持する。
使われ方：全左 Hom の単位族と全右関手族の相対評価の標的を一致させる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：元の二つの関手を固定した id→LR の全実単位空間。
方針：恒等関手の coslice の元の合成頂点上の fiber を取る。
規約：単位に随伴条件を課さない。
使われ方：左右の単位評価の共通標的。 -/
def PairFixedUnitSpace {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌) : SSet.{u + 1} :=
  vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj))))
    (functorVertex (leftVertexFunctor v ≫ rightVertexFunctor w))

instance pairFixedUnitSpace_kanComplex {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌) :
    KanComplex (PairFixedUnitSpace v w) := vertexFiber_kanComplex_of_leftFibration _ _

/-- 概要：右関手を固定した左単位 coslice の fiber は同じ実単位空間。
方針：保存条件の引き戻しと前合成の引き戻しの fiber 同型を順に使う。
規約：元の二つの関手の頂点を保持する。
使われ方：相対関手評価の標的の正規化。 -/
def pairLeftUnitFiberIso {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌) :
    vertexFiber (preservingLeftUnitProjection v) w ≅ PairFixedUnitSpace v w := by
  let q := sliceUnderProjection (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj)))
  let f := (pre (leftVertexFunctor v)).app C.obj
  let i := rightFunctorInclusion D C
  have hw : i.app (Opposite.op ⦋0⦌) w = functorVertex (rightVertexFunctor w) :=
    ((functorVertexEquiv D.obj C.obj).apply_symm_apply w.val).symm
  have h : f.app (Opposite.op ⦋0⦌) (i.app (Opposite.op ⦋0⦌) w) =
      functorVertex (leftVertexFunctor v ≫ rightVertexFunctor w) := by
    rw [hw]
    rfl
  exact vertexFiberPullbackIso (pullback.snd q f) i w ≪≫
    vertexFiberPullbackIso q f (i.app (Opposite.op ⦋0⦌) w) ≪≫
    eqToIso (congrArg (vertexFiber q) h)

/-- 概要：左関手を固定した右単位 coslice の fiber は同じ実単位空間。
方針：保存条件の引き戻しと後合成の引き戻しの fiber 同型を順に使う。
規約：同じ元の二関手と実単位を保持する。
使われ方：左 Hom の単位族の標的の正規化。 -/
def pairRightUnitFiberIso {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌) :
    vertexFiber (preservingRightUnitProjection w) v ≅ PairFixedUnitSpace v w := by
  let q := sliceUnderProjection (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj)))
  let f := (ihom C.obj).map (rightVertexFunctor w)
  let i := leftFunctorInclusion C D
  have hv : i.app (Opposite.op ⦋0⦌) v = functorVertex (leftVertexFunctor v) :=
    ((functorVertexEquiv C.obj D.obj).apply_symm_apply v.val).symm
  have h : f.app (Opposite.op ⦋0⦌) (i.app (Opposite.op ⦋0⦌) v) =
      functorVertex (leftVertexFunctor v ≫ rightVertexFunctor w) := by
    rw [hv]
    rfl
  exact vertexFiberPullbackIso (pullback.snd q f) i v ≪≫
    vertexFiberPullbackIso q f (i.app (Opposite.op ⦋0⦌) v) ≪≫
    eqToIso (congrArg (vertexFiber q) h)

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
