module
public import SerrePositivity.KST.Fibration.FirstVertexEdgewiseRestriction
public import SerrePositivity.KST.Fibration.StrictTransportOppositePointHom

/-! # 初頂点の解像上の底変換は、同じ pullback strict transport の反転成分を回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]

local instance : LeftFibration (pullback.snd p (transportSimplexFirstVertexMap B)) :=
  ⟨leftFibrations.pullback_snd p _ (LeftFibration.mem (p := p))⟩

/-- 元の解像の同じ底変換頂点は、元の pullback 射影の同じ反転比較対象。 -/
theorem firstVertexOppositeBaseChange_vertex :
    (leftFibrationEdgewiseFirstVertexBaseChange B).app (Opposite.op ⦋0⦌)
      (coherentNerveVertex (firstVertexComparisonObject p)) =
    coherentNerveVertex (strictTransportComparisonObject
      (pullback.snd p (transportSimplexFirstVertexMap B))) :=
  leftFibrationEdgewiseFirstVertexBaseChange_vertex B (leftFibrationObjectOf p)

/-- 底変換後の反転比較の始域値は、元の pullback strict 切断空間。 -/
theorem firstVertexOppositePre_source_vertex (c : TransportSimplexCategory B) :
    (kanEnrichedDoubleEvaluation (firstVertexComparisonObject p) c).app (Opposite.op ⦋0⦌)
        (functorVertex (leftFibrationEdgewiseFirstVertexBaseChange B ≫
          (edgewiseEnrichedInfinityMap (LeftFibrationObject (nerve (TransportSimplexCategory B))) ≫
            leftStraighteningCoherentMap (TransportSimplexCategory B)))) =
      spaceInfinityVertex ((leftStrictTransportFunctor
        (pullback.snd p (transportSimplexFirstVertexMap B))).obj c) := by
  let q := pullback.snd p (transportSimplexFirstVertexMap B)
  let F := edgewiseEnrichedInfinityMap (LeftFibrationObject (nerve (TransportSimplexCategory B))) ≫
    leftStraighteningCoherentMap (TransportSimplexCategory B)
  let x := coherentNerveVertex (strictTransportComparisonObject q)
  let a := ULift.up.{u + 1} (nerveVertex c)
  have hv := doubleFunctorEvaluation_precomp_vertex_of_eq F
    (leftFibrationEdgewiseFirstVertexBaseChange B)
    (coherentNerveVertex (firstVertexComparisonObject p)) a x
    (firstVertexOppositeBaseChange_vertex p)
  have hd := doubleFunctorEvaluation_vertex F x a
  have h₀ := congrArg ((evaluateFunctorAt (Y := SpaceInfinity.{u}) a).app (Opposite.op ⦋0⦌))
    (strictTransportOppositeSource_vertex q)
  have h₁ := evaluateFunctorAt_functorVertex a (leftStraighteningCandidate q)
  exact hv.trans (hd.trans (h₀.trans (h₁.trans (leftStraighteningCandidate_vertex q c))))

/-- 底変換後の反転比較の終域値は、元の同じ strict 切断空間の反転 Kan 値。 -/
theorem firstVertexOppositePre_target_vertex (c : TransportSimplexCategory B) :
    (kanEnrichedDoubleEvaluation (firstVertexComparisonObject p) c).app (Opposite.op ⦋0⦌)
        (functorVertex (leftFibrationEdgewiseFirstVertexBaseChange B ≫
          leftStraighteningOppositeCoherentMap (TransportSimplexCategory B))) =
      spaceInfinityVertex (kanObjectOpFunctor.obj ((leftStrictTransportFunctor
        (pullback.snd p (transportSimplexFirstVertexMap B))).obj c)) := by
  let q := pullback.snd p (transportSimplexFirstVertexMap B)
  let F := leftStraighteningOppositeCoherentMap (TransportSimplexCategory B)
  let x := coherentNerveVertex (strictTransportComparisonObject q)
  let a := ULift.up.{u + 1} (nerveVertex c)
  have hv := doubleFunctorEvaluation_precomp_vertex_of_eq F
    (leftFibrationEdgewiseFirstVertexBaseChange B)
    (coherentNerveVertex (firstVertexComparisonObject p)) a x
    (firstVertexOppositeBaseChange_vertex p)
  have hd := doubleFunctorEvaluation_vertex F x a
  have h₀ := congrArg ((evaluateFunctorAt (Y := SpaceInfinity.{u}) a).app (Opposite.op ⦋0⦌))
    (leftStraighteningOppositeCoherentMap_vertex q)
  have h₁ := evaluateFunctorAt_functorVertex a (leftCoherentTransport q)
  exact hv.trans (hd.trans (h₀.trans (h₁.trans
    (ScaffoldTransportComparisonSpan.coefficientResolutionVertexEq (p := q) c))))

/-- 元の解像上の反転比較の指定成分を、同じ二つの strict Kan 値で表示する。 -/
def firstVertexOppositePreChart (c : TransportSimplexCategory B) :=
  F2.isoNormalizeEndpoints
    (VertexIso.map ((leftStraighteningCoherentMap_oppositeIso
      (TransportSimplexCategory B)).precomp (leftFibrationEdgewiseFirstVertexBaseChange B))
      (kanEnrichedDoubleEvaluation (firstVertexComparisonObject p) c))
    (congrArg HomotopyCategory.mk (firstVertexOppositePre_source_vertex p c))
    (congrArg HomotopyCategory.mk (firstVertexOppositePre_target_vertex p c))

/-- 底変換後も、同じ元の strict transport の指定反転成分を厳密に回収する。 -/
theorem firstVertexOppositePreChart_eq (c : TransportSimplexCategory B) :
    firstVertexOppositePreChart p c = strictTransportOppositeComponentIso
      (pullback.snd p (transportSimplexFirstVertexMap B)) c := by
  have hm := functorIso_pre_doubleMap_of_vertex
    (leftStraighteningCoherentMap_oppositeIso (TransportSimplexCategory B))
    (leftFibrationEdgewiseFirstVertexBaseChange B)
    (coherentNerveVertex (firstVertexComparisonObject p)) (ULift.up (nerveVertex c))
    (coherentNerveVertex (strictTransportComparisonObject
      (pullback.snd p (transportSimplexFirstVertexMap B)))) (firstVertexOppositeBaseChange_vertex p)
  exact F2.isoNormalizeEndpoints_eq_of_heq _ _ _ _ (hm.trans
    (strictTransportOppositeComponentIso_heq_doubleMap
      (pullback.snd p (transportSimplexFirstVertexMap B)) c).symm)

end SerrePositivity.KST.Fibration
