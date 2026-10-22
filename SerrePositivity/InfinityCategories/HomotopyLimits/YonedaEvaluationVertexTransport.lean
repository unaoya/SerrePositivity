module

public import SerrePositivity.InfinityCategories.F1.CanonicalYonedaFiberTransport
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningMappingFiberTransport

/-!
概要：元の Yoneda 評価の実際の頂点を、同じ変換の値に沿う標準輸送へ比較する。
方針：元の全 Hom 比較の頂点を回収した相対射と厳密に同定し、既存の輸送比較を評価する。
規約：任意の変換頂点を扱い、元の恒等点と回収した変換辺を保持する。
使われ方：元の Yoneda の脚の恒等点像と、同じ反変側の輸送点の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の全 fiber Hom 比較の頂点は、同じ頂点から回収した元の相対射の fiber 作用。 -/
lemma unstraighteningFiberHom_vertex {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) (b : B _⦋0⦌) :
    (leftUnstraighteningMappingFiberHom F G b).app (Opposite.op ⦋0⦌) x =
      functorVertex (leftUnstraighteningPointedFiberMap F G
        (leftUnstraighteningMappingVertexMap F G x).val
        (leftUnstraighteningMappingVertexMap F G x).property b) := by
  change ((ihom (vertexFiber pointedSpaceProjection (F.app _ b))).map
      (leftUnstraighteningFiberIso G b).hom).app (Opposite.op ⦋0⦌)
    (((pre (leftUnstraighteningFiberIso F b).inv).app _).app (Opposite.op ⦋0⦌)
      ((relativeFunctorFiberHom (leftUnstraighteningProjection F)
        (leftUnstraighteningProjection G) b).app (Opposite.op ⦋0⦌)
          ((leftUnstraighteningMappingSpaceMap F G).app (Opposite.op ⦋0⦌) x))) = _
  rw [← leftUnstraighteningMappingVertexMap_vertex, relativeFunctorFiberHom_vertex]
  rfl

/-- 同じ恒等点での元の Yoneda 評価の頂点は、同じ回収射の実際の fiber 作用の値。 -/
lemma canonicalYonedaFiberEvaluation_vertex {C : SSet.{u}} [Quasicategory C]
    (y : C _⦋0⦌) (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})
    (x : (leftUnstraighteningTransformationSpace (representablePresheafInfinity y) F) _⦋0⦌) :
    (canonicalYonedaTransformationFiberEvaluation y F).app (Opposite.op ⦋0⦌) x =
      (leftUnstraighteningPointedFiberMap (representablePresheafInfinity y) F
        (leftUnstraighteningMappingVertexMap (representablePresheafInfinity y) F x).val
        (leftUnstraighteningMappingVertexMap (representablePresheafInfinity y) F x).property
        (ULift.up (SSet.opObjEquiv.symm y))).app (Opposite.op ⦋0⦌)
          (canonicalYonedaPointedIdentity y) := by
  change (evaluateFunctorAt (canonicalYonedaPointedIdentity y)).app (Opposite.op ⦋0⦌)
    ((leftUnstraighteningMappingFiberHom (representablePresheafInfinity y) F
      (ULift.up (SSet.opObjEquiv.symm y))).app (Opposite.op ⦋0⦌) x) = _
  rw [unstraighteningFiberHom_vertex, evaluateFunctorAt_functorVertex]

/-- 元の評価の実際の頂点は、同じ変換を評価した辺による恒等点の標準輸送と同型。 -/
def canonicalYonedaFiberEvaluation_vertexTransportIso
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})
    (x : (leftUnstraighteningTransformationSpace (representablePresheafInfinity y) F) _⦋0⦌) :
    VertexIso
      ((canonicalYonedaTransformationFiberEvaluation y F).app (Opposite.op ⦋0⦌) x)
      ((edgeTransport pointedSpaceProjection
        (functorEdgeAt (intervalMappingEdgeOfVertex x)
          (ULift.up (SSet.opObjEquiv.symm y)))).app (Opposite.op ⦋0⦌)
            (canonicalYonedaPointedIdentity y)) := by
  have h := (leftUnstraighteningMappingVertex_pointedFiberTransportIso
    (representablePresheafInfinity y) F x (ULift.up (SSet.opObjEquiv.symm y))).app
      (canonicalYonedaPointedIdentity y)
  rw [canonicalYonedaFiberEvaluation_vertex]
  exact h

end SerrePositivity.InfinityCategories.HomotopyLimits
