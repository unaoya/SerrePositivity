module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.PairCanonicalUnitPoint

/-!
概要：元の全単位族の実 Hom 作用を右頂点で評価し、同じ単位点で輸送すると同値。
方針：固定右の元の始単位からの全 Hom 輸送を、同じ pointed 比較の可換正方形へ送る。
規約：元の関手族の Hom 作用と同じ指定点を保持する。
使われ方：全単位族の充満忠実性を同じ点評価から検出する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：元の固定右の始単位を持ち上げた元の左頂点の fiber 点として保持する。
方針：元の単位の底の等式を宇宙持ち上げして零次定値の式へ続ける。
規約：元の単位点を変えない。
使われ方：指定点輸送の自然性への入力。 -/
def pairRightUnitInitialLiftedFiber {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (a : QCatAdjunction (leftVertexFunctor v) (rightVertexFunctor w)) :
    (vertexFiber ((SSet.uliftFunctor.{u + 2, u + 1}).map (preservingRightUnitProjection w))
      (ULift.up v)) _⦋0⦌ :=
  ⟨ULift.up (preservingRightUnitVertex v w a),
    (congrArg (ULift.up.{u + 2, u + 1}) (preservingRightUnitVertex_base v w a)).trans
      (pinchedConstant_zero
        (X := (SSet.uliftFunctor.{u + 2, u + 1}).obj (PrLFunctorSpace C D)) (ULift.up v)).symm⟩

/-- 概要：同じ持ち上げた元の始単位は元の固定右全空間の始対象。
方針：元の始対象性をそのまま宇宙持ち上げする。
規約：分類の値の始対象性と混同しない。
使われ方：元の左 Hom の指定点輸送の同値性。 -/
lemma pairRightUnitInitialLiftedFiber_isInitial {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (a : QCatAdjunction (leftVertexFunctor v) (rightVertexFunctor w)) :
    IsInitialVertex (pairRightUnitInitialLiftedFiber v w a).val :=
  (isInitialVertex_iff_ulift.{u + 1, u + 2} (preservingRightUnitVertex v w a)).mp
    (preservingRightUnitVertex_isInitial v w a)

/-- 概要：元の全関手族の評価後の実 Hom 作用に沿う輸送は同じ単位点で同値。
方針：固定右の元の始単位、同じ pointed 全空間比較、その実 fiber 同値を輸送自然性に適用する。
規約：元の Hom 作用と左右で共通の指定点のまま結論する。
使われ方：元の全関手族の充満忠実性の検出。 -/
lemma pairUnitEvaluatedTransport_isQCatEquivalence {C D : PresentableInfinityObject.{u}}
    (v₀ v₁ : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (a : QCatAdjunction (leftVertexFunctor v₀) (rightVertexFunctor w)) :
    IsQCatEquivalence
      (intervalMappingPostOfEq (pairUnitHomFamily C D ≫ evaluateFunctorAt (ULift.up w))
          (ULift.up v₀) (ULift.up v₁)
          (pairUnitHomFamily_evaluate_vertex v₀ w) (pairUnitHomFamily_evaluate_vertex v₁ w) ≫
        parametrizedFiberTransport pointedSpaceProjection
          ((pairUnitHomAtLeft v₀).app (Opposite.op ⦋0⦌) (ULift.up w))
          ((pairUnitHomAtLeft v₁).app (Opposite.op ⦋0⦌) (ULift.up w)) ≫
        evaluateFunctorAt (pairCanonicalUnitPoint v₀ w a)) := by
  let p := (SSet.uliftFunctor.{u + 2, u + 1}).map (preservingRightUnitProjection w)
  let f := pairRightUnitPointedDisplay w
  let g := pairUnitHomFamily C D ≫ evaluateFunctorAt (ULift.up w)
  have h : f ≫ pointedSpaceProjection = p ≫ g := by
    simpa only [f, p, g, pairUnitHomFamily_evaluate_right] using
      pairRightUnitPointedDisplay_projection w
  have hw : f.app (Opposite.op ⦋0⦌) (pairRightUnitInitialLiftedFiber v₀ w a).val =
      (pairCanonicalUnitPoint v₀ w a).val := (pairCanonicalUnitPoint_eq_rightDisplay v₀ w a).symm
  have hb : IsQCatEquivalence
      (transportSquareFiberMap p pointedSpaceProjection f g h (ULift.up v₁)) := by
    have aux : ∀ (g' : (SSet.uliftFunctor.{u + 2, u + 1}).obj
        (PrLFunctorSpace C D) ⟶ SpaceInfinity.{u + 1})
        (hg' : g' = pairUnitHomAtRight w)
        (h' : f ≫ pointedSpaceProjection = p ≫ g'),
        IsQCatEquivalence
          (transportSquareFiberMap p pointedSpaceProjection f g' h' (ULift.up v₁)) := by
      intro g' hg' h'
      subst g'
      exact pairRightUnitPointedDisplayFiber_isQCatEquivalence w v₁
    exact aux g (pairUnitHomFamily_evaluate_right w) h
  exact parametrizedPointTransport_square_isQCatEquivalence_of_initial
    p pointedSpaceProjection f g h (ULift.up v₀) (ULift.up v₁) _ _
    (pairUnitHomFamily_evaluate_vertex v₀ w) (pairUnitHomFamily_evaluate_vertex v₁ w)
    (pairRightUnitInitialLiftedFiber v₀ w a) (pairRightUnitInitialLiftedFiber_isInitial v₀ w a)
    (pairCanonicalUnitPoint v₀ w a) hw hb

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
