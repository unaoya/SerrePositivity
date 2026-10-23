module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeHomPointedEvaluationInterval
public import SerrePositivity.InfinityCategories.F1.Transport.DiagonalFiberTransport

/-!
概要：元の pointed 回収を、実際の coherent 評価に沿う同じ恒等点の輸送と比較する。
方針：既存の unstraightening の普遍 prism の厳密な始点・終点・底に一意性を適用する。
規約：全 coherent 変換空間で一つの関手同型を構成する。
使われ方：元の Kan 値回収との照合を、同じ右 Hom の恒等点での輸送へ帰着する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 実際の pointed 回収は、元の coherent 評価の区間族に沿う恒等点の輸送と同型。 -/
def relativeHomCoherentPointedRecovery_transportIso {B : SSet.{u}}
    (a q : LeftFibrationObject B) :
    FunctorIso (relativeHomCoherentPointedRecovery a q)
      (diagonalFiberTransport pointedSpaceProjection
        (SSet.const (relativeHomPointedIdentity q))
        (relativeHomPointedEvaluationInterval a q)) := by
  let c := relativeHomPointedEvaluationInterval a q
  have e := leftFibrationPrism_diagonalTransportIso pointedSpaceProjection
    (SSet.const (relativeHomPointedIdentity q)) (relativeHomCoherentPointedRecovery a q)
    (intervalMappingUncurry c) (intervalMappingUncurry_zero c) (intervalMappingUncurry_one c)
    (relativeHomPointedRecoveryPrism a q) (relativeHomPointedRecoveryPrism_zero a q)
    (relativeHomPointedRecoveryPrism_one a q)
    ((relativeHomPointedRecoveryPrism_projection a q).trans
      (relativeHomPointedEvaluationInterval_uncurry a q).symm)
  have hc : intervalMappingCurryOfEndpoints (intervalMappingUncurry c)
      (intervalMappingUncurry_zero c) (intervalMappingUncurry_one c) = c := by
    apply intervalMappingUncurry_injective _ _
    exact intervalMappingUncurry_curryOfEndpoints _ _ _
  rw [hc] at e
  exact e

/-- Kan 空間間の元の右 Hom の区間族に沿って、指定した pointed 点を評価する。 -/
def pointedRightHomEvaluate (K L : KanObject.{u})
    (x : (vertexFiber pointedSpaceProjection (spaceInfinityVertex K)) _⦋0⦌) :
    pinchedHom (coherentNerveVertex K) (coherentNerveVertex L) ⟶
      vertexFiber pointedSpaceProjection (spaceInfinityVertex L) :=
  diagonalFiberTransport pointedSpaceProjection (SSet.const x)
    (pinchedHomToIntervalMappingSpace (coherentNerveVertex K) (coherentNerveVertex L) ≫
      intervalMappingPostOfEq (𝟙 SpaceInfinity.{u}) (coherentNerveVertex K) (coherentNerveVertex L)
        (spaceInfinityVertex_eq_coherent K).symm (spaceInfinityVertex_eq_coherent L).symm)

/-- 実際の pointed 回収は、元の coherent 評価に続く同じ右 Hom の恒等点評価と同型。 -/
def relativeHomCoherentPointedRecovery_evaluateIso {B : SSet.{u}}
    (a q : LeftFibrationObject B) :
    FunctorIso (relativeHomCoherentPointedRecovery a q)
      (relativeHomCoherentEvaluationMap a q q ≫
        pointedRightHomEvaluate (relativeHomIdentityKanObject q)
          ((relativeFunctorEnrichedEvaluation a.val).obj q) (relativeHomPointedIdentity q)) := by
  have h : relativeHomCoherentEvaluationMap a q q ≫
      pointedRightHomEvaluate (relativeHomIdentityKanObject q)
        ((relativeFunctorEnrichedEvaluation a.val).obj q) (relativeHomPointedIdentity q) =
      diagonalFiberTransport pointedSpaceProjection
        (SSet.const (relativeHomPointedIdentity q)) (relativeHomPointedEvaluationInterval a q) := by
    rw [pointedRightHomEvaluate, diagonalFiberTransport_precomp, SSet.comp_const]
    rfl
  rw [h]
  exact relativeHomCoherentPointedRecovery_transportIso a q

end SerrePositivity.InfinityCategories
