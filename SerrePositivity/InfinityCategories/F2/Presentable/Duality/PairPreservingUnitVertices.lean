module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.PairInitialRestriction

/-!
概要：指定随伴の元の単位を、保存関手上の左右の固定 coslice の始対象として保持する。
方針：既存の実単位頂点を保存条件付きの引き戻しへ持ち上げ、境界充填を制限する。
規約：同じ左右の関手と同じ実単位を使う。
使われ方：単位の二変数族の実際の相対評価の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：指定随伴の実単位を元の右保存関手圏上の固定左 coslice に持ち上げる。
方針：元の単位頂点と元の右頂点を同じ引き戻しに束ねる。
規約：単位の高次データを離散化しない。
使われ方：右関手族の単位評価の基準点。 -/
def preservingLeftUnitVertex {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (a : QCatAdjunction (leftVertexFunctor v) (rightVertexFunctor w)) :
    PreservingLeftUnitCoslice v _⦋0⦌ :=
  SSet.yonedaEquiv (pullback.lift (SSet.yonedaEquiv.symm (leftUnitVertex a))
    (SSet.yonedaEquiv.symm w) (by
      rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, leftUnitVertex_base]
      exact congrArg SSet.yonedaEquiv.symm
        ((functorVertexEquiv D.obj C.obj).apply_symm_apply w.val)))

/-- 概要：持ち上げた固定左の単位頂点は元の全関手 coslice の同じ頂点を保持する。
方針：同じ引き戻しの第一脚を計算する。
規約：元の頂点の厳密な等式。
使われ方：元の始対象性の制限。 -/
lemma preservingLeftUnitVertex_full {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (a : QCatAdjunction (leftVertexFunctor v) (rightVertexFunctor w)) :
    (pullback.fst _ (rightFunctorInclusion D C)).app (Opposite.op ⦋0⦌)
      (preservingLeftUnitVertex v w a) = leftUnitVertex a := by
  dsimp only [preservingLeftUnitVertex, PreservingLeftUnitCoslice]
  rw [← SSet.yonedaEquiv_comp, pullback.lift_fst, Equiv.apply_symm_apply]

/-- 概要：固定左の単位頂点の射影は指定した元の右頂点。
方針：引き戻しの第二脚と Yoneda の往復を計算する。
規約：元の頂点の厳密な等式。
使われ方：単位評価の標的の fiber を固定する。 -/
lemma preservingLeftUnitVertex_base {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (a : QCatAdjunction (leftVertexFunctor v) (rightVertexFunctor w)) :
    (preservingLeftUnitProjection v).app (Opposite.op ⦋0⦌)
      (preservingLeftUnitVertex v w a) = w := by
  dsimp only [preservingLeftUnitVertex, preservingLeftUnitProjection, PreservingLeftUnitCoslice]
  rw [← SSet.yonedaEquiv_comp, pullback.lift_snd, Equiv.apply_symm_apply]

/-- 概要：元の随伴単位は右保存関手上の固定左 coslice の始対象。
方針：元の全関手 coslice の始対象の境界充填を全部分圏の引き戻しへ制限する。
規約：全右保存関手と全自然変換を許す。
使われ方：右関手族に自然な単位評価の同値性。 -/
lemma preservingLeftUnitVertex_isInitial {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (a : QCatAdjunction (leftVertexFunctor v) (rightVertexFunctor w)) :
    IsInitialVertex (preservingLeftUnitVertex v w a) := by
  apply initialVertex_pullback_fullSubcomplex
  exact (congrArg IsInitialVertex (preservingLeftUnitVertex_full v w a)).mpr
    (leftUnitVertex_isInitial a)

/-- 概要：指定随伴の実単位を元の左保存関手圏上の固定右 coslice に持ち上げる。
方針：元の単位頂点と元の左頂点を同じ引き戻しに束ねる。
規約：元の実単位を選び直さない。
使われ方：左関手族の単位評価の基準点。 -/
def preservingRightUnitVertex {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (a : QCatAdjunction (leftVertexFunctor v) (rightVertexFunctor w)) :
    PreservingRightUnitCoslice w _⦋0⦌ :=
  SSet.yonedaEquiv (pullback.lift (SSet.yonedaEquiv.symm (rightUnitVertex a))
    (SSet.yonedaEquiv.symm v) (by
      rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, rightUnitVertex_base]
      exact congrArg SSet.yonedaEquiv.symm
        ((functorVertexEquiv C.obj D.obj).apply_symm_apply v.val)))

/-- 概要：持ち上げた固定右の単位頂点は元の全関手 coslice の同じ頂点を保持する。
方針：同じ引き戻しの第一脚を計算する。
規約：元の頂点の厳密な等式。
使われ方：元の始対象性の制限。 -/
lemma preservingRightUnitVertex_full {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (a : QCatAdjunction (leftVertexFunctor v) (rightVertexFunctor w)) :
    (pullback.fst _ (leftFunctorInclusion C D)).app (Opposite.op ⦋0⦌)
      (preservingRightUnitVertex v w a) = rightUnitVertex a := by
  dsimp only [preservingRightUnitVertex, PreservingRightUnitCoslice]
  rw [← SSet.yonedaEquiv_comp, pullback.lift_fst, Equiv.apply_symm_apply]

/-- 概要：固定右の単位頂点の射影は指定した元の左頂点。
方針：引き戻しの第二脚と Yoneda の往復を計算する。
規約：元の頂点の厳密な等式。
使われ方：点 Hom の始域を元の左頂点で表示する。 -/
lemma preservingRightUnitVertex_base {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (a : QCatAdjunction (leftVertexFunctor v) (rightVertexFunctor w)) :
    (preservingRightUnitProjection w).app (Opposite.op ⦋0⦌)
      (preservingRightUnitVertex v w a) = v := by
  dsimp only [preservingRightUnitVertex, preservingRightUnitProjection, PreservingRightUnitCoslice]
  rw [← SSet.yonedaEquiv_comp, pullback.lift_snd, Equiv.apply_symm_apply]

/-- 概要：元の随伴単位は左保存関手上の固定右 coslice の始対象。
方針：元の全関手 coslice の始対象の境界充填を保存関手の引き戻しへ制限する。
規約：全左保存関手の全自然変換を許す。
使われ方：左関手族の実際の単位評価の同値性。 -/
lemma preservingRightUnitVertex_isInitial {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (a : QCatAdjunction (leftVertexFunctor v) (rightVertexFunctor w)) :
    IsInitialVertex (preservingRightUnitVertex v w a) := by
  apply initialVertex_pullback_fullSubcomplex
  exact (congrArg IsInitialVertex (preservingRightUnitVertex_full v w a)).mpr
    (rightUnitVertex_isInitial a)

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
