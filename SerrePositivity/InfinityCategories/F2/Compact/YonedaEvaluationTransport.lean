module

public import SerrePositivity.InfinityCategories.F2.Compact.YonedaEvaluationCoslice
public import SerrePositivity.InfinityCategories.F1.Joins.CosliceUniversalPrismTransport
public import SerrePositivity.InfinityCategories.F1.Transport.DiagonalFiberTransportSquareVertices

/-!
概要：元の Yoneda 評価の大域比較の fiber 作用を、指定恒等点からの全区間輸送へ同定。
方針：元の普遍 coslice prism と unstraightening の引き戻し正方形の自然性を合成。
規約：同じ大域射・同じ恒等点・元の全写像空間を保つ。
使われ方：大域射の fiber 同値性を既存の全 Yoneda 評価で検出する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 正規化した fiber 同型は、元の unstraightening 正方形の直接の fiber 射そのもの。 -/
lemma yonedaEvaluationFiberIso_squareMap {C : SSet.{u}} (y : C _⦋0⦌)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) :
    transportSquareFiberMap (leftUnstraighteningProjection (presheafInfinityEvaluation y))
      pointedSpaceProjection (pullback.fst pointedSpaceProjection (presheafInfinityEvaluation y))
      (presheafInfinityEvaluation y) pullback.condition (functorVertex F) ≫
      eqToHom (congrArg (vertexFiber pointedSpaceProjection)
        (yonedaEvaluation_value y F)) =
      (yonedaEvaluationFiberIso y F).hom := by
  apply (cancel_mono (vertexFiberι pointedSpaceProjection
    (F.app _ (ULift.up (SSet.opObjEquiv.symm y))))).mp
  rw [Category.assoc, vertexFiberTransport_ι pointedSpaceProjection
    (yonedaEvaluation_value y F), transportSquareFiberMap_ι]
  dsimp only [yonedaEvaluationFiberIso, Iso.trans_hom, eqToIso.hom]
  rw [Category.assoc, vertexFiberTransport_ι pointedSpaceProjection
    (yonedaEvaluation_value y F)]
  exact (leftUnstraighteningFiberIso_hom_ι (presheafInfinityEvaluation y) (functorVertex F)).symm

/-- 実際の大域比較の fiber 作用は、同じ指定始点からの元の coslice 区間族の輸送。 -/
def yonedaEvaluationCosliceFiber_nativeTransportIso {C : SSet.{u}} [Quasicategory C]
    (y : C _⦋0⦌)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) :
    FunctorIso (yonedaEvaluationCosliceFiber y F)
      (diagonalFiberTransport (leftUnstraighteningProjection (presheafInfinityEvaluation y))
        (SSet.const (yonedaEvaluationIdentity y))
        (cosliceFiberToIntervalMappingSpace
          (functorVertex (representablePresheafInfinity y)) (functorVertex F)) ≫
        (yonedaEvaluationFiberIso y F).hom) :=
  FunctorIso.postcomp
    (leftFibrationCosliceMap_transportIso
      (leftUnstraighteningProjection (presheafInfinityEvaluation y))
      (functorVertex (representablePresheafInfinity y)) (yonedaEvaluationIdentity y).val
      (yonedaEvaluationIdentity_projection y) (yonedaEvaluationCosliceMap y)
      (yonedaEvaluationCosliceMap_projection y) (yonedaEvaluationCosliceMap_identity y)
      (functorVertex F)) (yonedaEvaluationFiberIso y F).hom

/-- 元の大域比較の pointed fiber 作用は、元の評価後の恒等点からの全区間輸送。 -/
def yonedaEvaluationCosliceFiber_pointedTransportIso {C : SSet.{u}} [Quasicategory C]
    (y : C _⦋0⦌)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) :
    FunctorIso (yonedaEvaluationCosliceFiber y F)
      (diagonalFiberTransport pointedSpaceProjection (SSet.const (canonicalYonedaPointedIdentity y))
        (cosliceFiberToIntervalMappingSpace
          (functorVertex (representablePresheafInfinity y)) (functorVertex F) ≫
          intervalMappingPostOfEq (presheafInfinityEvaluation y)
            (functorVertex (representablePresheafInfinity y)) (functorVertex F)
            (yonedaEvaluation_value y _) (yonedaEvaluation_value y _))) := by
  have e := diagonalFiberTransport_squareOfEqIso
    (leftUnstraighteningProjection (presheafInfinityEvaluation y)) pointedSpaceProjection
    (pullback.fst pointedSpaceProjection (presheafInfinityEvaluation y))
    (presheafInfinityEvaluation y) pullback.condition
    (yonedaEvaluation_value y (representablePresheafInfinity y))
    (yonedaEvaluation_value y F) (SSet.const (yonedaEvaluationIdentity y))
    (cosliceFiberToIntervalMappingSpace
      (functorVertex (representablePresheafInfinity y)) (functorVertex F))
  rw [yonedaEvaluationFiberIso_squareMap, yonedaEvaluationFiberIso_squareMap,
    SSet.const_comp, yonedaEvaluationIdentity_pointed] at e
  exact yonedaEvaluationCosliceFiber_nativeTransportIso y F ≪≫ e

end SerrePositivity.InfinityCategories.F2.Compact
