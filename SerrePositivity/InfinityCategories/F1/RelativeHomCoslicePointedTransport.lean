module

public import SerrePositivity.InfinityCategories.F1.RelativeHomCosliceTransport
public import SerrePositivity.InfinityCategories.F1.DiagonalFiberTransportSquareVertices

/-!
概要：Hom 関手の大域比較の fiber 作用を、実際の pointed-space の標準輸送へ移す。
方針：unstraightening の引き戻し正方形に同じ対角輸送の自然性を適用する。
規約：元の恒等点と標準 Kan 頂点を厳密に回収し、反転係数の同一視は行わない。
使われ方：coherent な Hom の区間族と、恒等射に作用する Kan の合成の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 引き戻し正方形の正規化した直接の fiber 射は、既存の同じ fiber 同型の順方向。 -/
lemma relativeHomUnstraighteningFiberIso_squareMap {B : SSet.{u}}
    (q r : LeftFibrationObject B) :
    transportSquareFiberMap
      (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val))
      pointedSpaceProjection (pullback.fst pointedSpaceProjection
        (leftFibrationCoherentEvaluation q.val)) (leftFibrationCoherentEvaluation q.val)
      (pullback.condition) (coherentNerveVertex r) ≫
      eqToHom (congrArg (vertexFiber pointedSpaceProjection)
        (relativeHomCoherentEvaluation_value q r)) =
      (relativeHomUnstraighteningFiberIso q r).hom := by
  apply (cancel_mono (vertexFiberι pointedSpaceProjection
    (spaceInfinityVertex ((relativeFunctorEnrichedEvaluation q.val).obj r)))).1
  rw [Category.assoc, vertexFiberTransport_ι pointedSpaceProjection
    (relativeHomCoherentEvaluation_value q r), transportSquareFiberMap_ι,
    relativeHomUnstraighteningFiberIso_hom_ι]

/-- 実際の大域比較の pointed fiber 作用は、元の恒等点からの同じ区間族の輸送。 -/
def relativeHomCosliceComparisonFiber_pointedTransportIso {B : SSet.{u}}
    (q r : LeftFibrationObject B) :
    FunctorIso (relativeHomCosliceComparisonFiber q r)
      (diagonalFiberTransport pointedSpaceProjection (SSet.const (relativeHomPointedIdentity q))
        (cosliceFiberToIntervalMappingSpace (coherentNerveVertex q) (coherentNerveVertex r) ≫
          intervalMappingPostOfEq (leftFibrationCoherentEvaluation q.val)
            (coherentNerveVertex q) (coherentNerveVertex r)
            (relativeHomCoherentEvaluation_value q q)
            (relativeHomCoherentEvaluation_value q r))) := by
  have e := diagonalFiberTransport_squareOfEqIso
    (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val))
    pointedSpaceProjection (pullback.fst pointedSpaceProjection
      (leftFibrationCoherentEvaluation q.val)) (leftFibrationCoherentEvaluation q.val)
    (pullback.condition) (relativeHomCoherentEvaluation_value q q)
    (relativeHomCoherentEvaluation_value q r) (SSet.const (relativeHomUnstraighteningIdentity q))
    (cosliceFiberToIntervalMappingSpace (coherentNerveVertex q) (coherentNerveVertex r))
  rw [relativeHomUnstraighteningFiberIso_squareMap,
    relativeHomUnstraighteningFiberIso_squareMap, SSet.const_comp,
    relativeHomUnstraighteningIdentity_pointed] at e
  exact relativeHomCosliceComparisonFiber_nativeTransportIso q r ≪≫ e

end SerrePositivity.InfinityCategories
