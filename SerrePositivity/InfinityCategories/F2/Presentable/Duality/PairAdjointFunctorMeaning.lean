module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.PairAdjointFunctorVertices
public import SerrePositivity.InfinityCategories.F1.Categories.OppositeFunctorIso

/-!
概要：元の反変単体写像の値が元の左関手の実際の右随伴であることを回収する。
方針：元の反対全関手圏の頂点同型を解除し、元の全関手圏の同型で随伴を輸送する。
規約：元の左関手を同型で置き換えない。
使われ方：対ごとの双対性の随伴対応としての意味。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：元の反変作用の値を元の右関手として読む。
方針：右関手圏の反対の頂点を解除して元の関手に戻す。
規約：同じ単体写像の元の値を使う。
使われ方：実際の随伴の型の表示。 -/
def pairRightAdjointValue {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) : D.obj ⟶ C.obj :=
  rightVertexFunctor (SSet.opObjEquiv
    ((pairRightAdjointFunctor C D).app (Opposite.op ⦋0⦌) v))

/-- 概要：元の反変作用の右関手値は、指定した元の右随伴と自然同型。
方針：反対全関手圏の頂点同型を二重反転で戻し、元の全部分圏の包含に通す。
規約：全関手圏内の同型であり、自然変換の可逆性を保つ。
使われ方：元の随伴の右側だけを同じ値に輸送する。 -/
def pairRightAdjointValueIso {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (a : QCatAdjunction (leftVertexFunctor v) (rightVertexFunctor w)) :
    FunctorIso (pairRightAdjointValue v) (rightVertexFunctor w) := by
  let t := SSet.opObjEquiv ((pairRightAdjointFunctor C D).app (Opposite.op ⦋0⦌) v)
  have e := VertexIso.map (VertexIso.op (pairRightAdjointFunctor_vertexIso v w a))
    (SSet.opFunctorCompOpFunctorIso.app (PrRFunctorSpace D C)).hom
  change VertexIso t w at e
  have ei := VertexIso.map e (rightFunctorInclusion D C)
  have ht : functorVertex (rightVertexFunctor t) =
      (rightFunctorInclusion D C).app (Opposite.op ⦋0⦌) t :=
    (functorVertexEquiv D.obj C.obj).apply_symm_apply t.val
  have hw : functorVertex (rightVertexFunctor w) =
      (rightFunctorInclusion D C).app (Opposite.op ⦋0⦌) w :=
    (functorVertexEquiv D.obj C.obj).apply_symm_apply w.val
  exact eqToIso (congrArg HomotopyCategory.mk ht) ≪≫ ei ≪≫
    eqToIso (congrArg HomotopyCategory.mk hw.symm)

/-- 概要：構成した元の反変作用の各値は、元の左関手の実際の右随伴。
方針：d で得た指定右随伴との元の関手同型で右側だけを輸送する。
規約：元の左関手と同じ単体写像の右値を保持する。
使われ方：対ごとの同値の随伴対応としての公開界面。 -/
def pairRightAdjointFunctorAdjunction {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) :
    QCatAdjunction (leftVertexFunctor v) (pairRightAdjointValue v) := by
  let w := rightAdjointVertex v
  have a : QCatAdjunction (leftVertexFunctor v) (rightVertexFunctor w) := by
    simpa only [w, rightAdjointVertex, rightFunctorVertex, rightVertexFunctor,
      Equiv.symm_apply_apply] using chosenRightAdjunction v
  exact qcatAdjunctionChangeRight a (pairRightAdjointValueIso v w a).symm

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
