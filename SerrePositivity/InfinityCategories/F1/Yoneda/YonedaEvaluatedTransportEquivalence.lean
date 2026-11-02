module

public import SerrePositivity.InfinityCategories.F1.Transport.ParametrizedPointTransportSquare
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.SourceInitial
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.SourcePointedFiber

/-!
概要：同じ Yoneda 写像の指定点評価に沿う普遍輸送は、同じ恒等点で評価すると同値。
方針：始点固定の Tw の恒等点からの輸送と、その実際の pointed 比較の fiber 同値を使う。
規約：c1 が使う同じ pointed 恒等点と、元の Yoneda 写像の区間後合成を保持する。
使われ方：同じ Yoneda 写像の Hom 作用に恒等点評価を続けた射の同値性を結論する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 同じ Yoneda 写像の指定点での頂点の評価は、同じ対象前層の実際の値。 -/
lemma yonedaInfinityMap_evaluate_vertex {C : SSet.{u}} [Quasicategory C]
    (x y : C _⦋0⦌) :
    (yonedaInfinityMap C ≫ evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm x))).app
      (Opposite.op ⦋0⦌) (ULift.up y) =
    (representablePresheafInfinity y).app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm x)) := by
  change (evaluateFunctorAt _).app _ ((yonedaInfinityMap C).app _ (ULift.up y)) = _
  rw [yonedaInfinityMap_vertex, evaluateFunctorAt_functorVertex]

/-- 始点固定の同じ Tw 恒等点を、持ち上げた元の底の指定 fiber 内の点として表示する。 -/
def twistedArrowSourceIdentityLiftedFiber {C : SSet.{u}} (x : C _⦋0⦌) :
    (vertexFiber ((SSet.uliftFunctor.{u + 1, u}).map (twistedArrowSourceProjection x))
      (ULift.up x)) _⦋0⦌ :=
  ⟨ULift.up (twistedArrowSourceIdentity x),
    (congrArg (ULift.up.{u + 1, u}) (twistedArrowSourceIdentity_projection x)).trans
      (pinchedConstant_zero (X := (SSet.uliftFunctor.{u + 1, u}).obj C) (ULift.up x)).symm⟩

/-- 同じ指定点は、持ち上げた Tw の始点固定の全空間でも始対象。 -/
lemma twistedArrowSourceIdentityLiftedFiber_isInitialVertex
    {C : SSet.{u}} [Quasicategory C] (x : C _⦋0⦌) :
    IsInitialVertex (twistedArrowSourceIdentityLiftedFiber x).val :=
  (isInitialVertex_iff_ulift.{u, u + 1} (twistedArrowSourceIdentity x)).mp
    (twistedArrowSourceIdentity_isInitialVertex x)

/-- 同じ Yoneda 指定点評価に沿う全区間パラメーターの輸送を、同じ恒等点で評価すると同値。 -/
lemma yonedaInfinityEvaluatedTransport_isQCatEquivalence
    {C : SSet.{u}} [Quasicategory C] (x y : C _⦋0⦌) :
    IsQCatEquivalence
      (intervalMappingPostOfEq
          (yonedaInfinityMap C ≫ evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm x)))
          (ULift.up x) (ULift.up y)
          (yonedaInfinityMap_evaluate_vertex x x) (yonedaInfinityMap_evaluate_vertex x y) ≫
        parametrizedFiberTransport pointedSpaceProjection
          ((representablePresheafInfinity x).app _ (ULift.up (SSet.opObjEquiv.symm x)))
          ((representablePresheafInfinity y).app _ (ULift.up (SSet.opObjEquiv.symm x))) ≫
        evaluateFunctorAt (canonicalYonedaPointedIdentity x)) := by
  exact parametrizedPointTransport_square_isQCatEquivalence_of_initial
    ((SSet.uliftFunctor.{u + 1, u}).map (twistedArrowSourceProjection x))
    pointedSpaceProjection (twistedArrowSourcePointedDisplay x)
    (yonedaInfinityMap C ≫ evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm x)))
    (twistedArrowSourcePointedDisplay_projection x) (ULift.up x) (ULift.up y) _ _
    (yonedaInfinityMap_evaluate_vertex x x) (yonedaInfinityMap_evaluate_vertex x y)
    (twistedArrowSourceIdentityLiftedFiber x)
    (twistedArrowSourceIdentityLiftedFiber_isInitialVertex x)
    (canonicalYonedaPointedIdentity x) (canonicalYonedaPointedIdentity_eq_sourceDisplay x).symm
    (twistedArrowSourcePointedDisplayFiber_isQCatEquivalence x y)

end SerrePositivity.InfinityCategories
