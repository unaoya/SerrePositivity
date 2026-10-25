module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.PairFunctorVertexEvaluation
public import SerrePositivity.InfinityCategories.Core.UniverseEdgeTransport

/-!
概要：構成した同じ反変関手の各頂点を元の右随伴と比較し、本質的全射性を証明する。
方針：全自然な Yoneda 比較を頂点で評価し、充満忠実性と宇宙降下を使う。
規約：写像空間だけの結果へ弱めず、元の実際の反変単体写像について証明する。
使われ方：対ごとの全関手圏同値の存在側。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：持ち上げた実際の反変作用の値は、指定した元の右随伴と同型。
方針：同じ Yoneda 比較の成分と指定右随伴による表現可能性を充満忠実性で戻す。
規約：右随伴を別の射の値として比較しない。
使われ方：元の宇宙へ降ろす前の頂点の意味の回収。 -/
def pairRightAdjointFunctorLifted_vertexIso {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (a : QCatAdjunction (leftVertexFunctor v) (rightVertexFunctor w)) :
    VertexIso
      ((pairRightAdjointFunctorLifted C D).app (Opposite.op ⦋0⦌) (ULift.up v))
      (ULift.up (SSet.opObjEquiv.symm w)) := by
  let y := pairCovariantYoneda (PrRFunctorSpace D C)
  let x := (pairRightAdjointFunctorLifted C D).app (Opposite.op ⦋0⦌) (ULift.up v)
  let z := ULift.up (SSet.opObjEquiv.symm w)
  have e₀ : VertexIso (y.app (Opposite.op ⦋0⦌) x)
      ((pairUnitHomFamily C D).app (Opposite.op ⦋0⦌) (ULift.up v)) :=
    pairCompositeFunctorIsoVertex (pairRightAdjointFunctorLifted_yonedaIso C D) (ULift.up v)
  have e₁ : VertexIso ((pairUnitHomFamily C D).app (Opposite.op ⦋0⦌) (ULift.up v))
      (functorVertex (pairUnitHomAtLeft v)) :=
    eqToIso (congrArg HomotopyCategory.mk (pairUnitHomFamily_vertex v))
  have hz : y.app (Opposite.op ⦋0⦌) z =
      functorVertex (covariantRepresentableInfinity w) := by
    simpa only [Equiv.apply_symm_apply] using
      pairCovariantYoneda_vertex (SSet.opObjEquiv.symm w)
  have e₂ : VertexIso (functorVertex (covariantRepresentableInfinity w))
      (y.app (Opposite.op ⦋0⦌) z) := eqToIso (congrArg HomotopyCategory.mk hz.symm)
  exact pairCovariantYonedaPreimageVertexIso (PrRFunctorSpace D C)
    (e₀ ≪≫ e₁ ≪≫ (pairUnitHomAtLeft_representationIso v w a).symm ≪≫ e₂)

/-- 概要：元の全関手圏間の実際の反変作用の値は、指定右随伴の元の頂点と同型。
方針：持ち上げた頂点同型を降下し、同じ単体写像の厳密な持ち上げ公式で正規化する。
規約：元の反対全関手圏の同型。
使われ方：本質的全射性と元の随伴の意味の回収。 -/
def pairRightAdjointFunctor_vertexIso {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (a : QCatAdjunction (leftVertexFunctor v) (rightVertexFunctor w)) :
    VertexIso ((pairRightAdjointFunctor C D).app (Opposite.op ⦋0⦌) v)
      (SSet.opObjEquiv.symm w) := by
  have e := (UniverseEdge.downFunctor (PrRFunctorSpace D C).op).mapIso
    (pairRightAdjointFunctorLifted_vertexIso v w a)
  have hd := congrArg
    (fun f : (SSet.uliftFunctor.{u + 2, u + 1}).obj (PrLFunctorSpace C D) ⟶
        (SSet.uliftFunctor.{u + 2, u + 1}).obj (PrRFunctorSpace D C).op ↦
      (f.app (Opposite.op ⦋0⦌) (ULift.up v)).down)
    (pairRightAdjointFunctor_ulift C D)
  change (pairRightAdjointFunctor C D).app (Opposite.op ⦋0⦌) v =
    ((pairRightAdjointFunctorLifted C D).app (Opposite.op ⦋0⦌) (ULift.up v)).down at hd
  change VertexIso
    (((pairRightAdjointFunctorLifted C D).app (Opposite.op ⦋0⦌) (ULift.up v)).down)
    (SSet.opObjEquiv.symm w) at e
  rw [← hd] at e
  exact e

/-- 概要：元の反変随伴関手は全右関手圏の反対へ本質的全射。
方針：d による元の右関手の左随伴を取り、同じ反変作用の頂点比較を使う。
規約：元の実際の単体写像についての結論。
使われ方：全関手圏の対ごとの同値の存在側。 -/
lemma pairRightAdjointFunctor_isEssentiallySurjective (C D : PresentableInfinityObject.{u}) :
    IsEssentiallySurjective (pairRightAdjointFunctor C D) := by
  intro w
  let w' : PrRFunctorSpace D C _⦋0⦌ := SSet.opObjEquiv w
  let v := leftAdjointVertex w'
  have a : QCatAdjunction (leftVertexFunctor v) (rightVertexFunctor w') := by
    simpa only [v, leftAdjointVertex, leftFunctorVertex, leftVertexFunctor,
      Equiv.symm_apply_apply] using chosenLeftAdjunction w'
  refine ⟨v, ⟨?_⟩⟩
  exact pairRightAdjointFunctor_vertexIso v w' a ≪≫
    eqToIso (congrArg HomotopyCategory.mk (SSet.opObjEquiv.symm_apply_apply w))

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
