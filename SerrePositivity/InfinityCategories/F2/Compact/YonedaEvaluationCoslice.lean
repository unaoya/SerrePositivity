module

public import SerrePositivity.InfinityCategories.F1.CanonicalYonedaFiberTransport
public import SerrePositivity.InfinityCategories.F1.CosliceUniversalPrismLift
public import SerrePositivity.InfinityCategories.F1.PresheafInfinity

/-!
概要：元の Yoneda 対象の coslice から、元の前層評価の unstraightening への一つの大域射。
方針：全体から取った同じ恒等点を始点 fiber へ戻し、同じ普遍 coslice prism を延長。
規約：指定恒等点と底への射影を厳密に保持する。同値性は次の工程で証明する。
使われ方：Yoneda 像の compact 性に必要な全 Hom 関手と全評価の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の前層評価は、指定した全関手の同じ頂点値を厳密に回収する。 -/
lemma yonedaEvaluation_value {C : SSet.{u}} (y : C _⦋0⦌)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) :
    (presheafInfinityEvaluation y).app (Opposite.op ⦋0⦌) (functorVertex F) =
      F.app (Opposite.op ⦋0⦌) (ULift.up (SSet.opObjEquiv.symm y)) :=
  evaluateFunctorAt_functorVertex _ F

/-- 評価の全空間の fiber を、元の前層の指定値の pointed fiber へ厳密に戻す同型。 -/
def yonedaEvaluationFiberIso {C : SSet.{u}} (y : C _⦋0⦌)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) :
    vertexFiber (leftUnstraighteningProjection (presheafInfinityEvaluation y)) (functorVertex F) ≅
      vertexFiber pointedSpaceProjection (F.app _ (ULift.up (SSet.opObjEquiv.symm y))) :=
  leftUnstraighteningFiberIso (presheafInfinityEvaluation y) (functorVertex F) ≪≫
    eqToIso (congrArg (vertexFiber pointedSpaceProjection) (yonedaEvaluation_value y F))

/-- 評価の全空間の、元の Yoneda 対象上にある同じ恒等点。 -/
def yonedaEvaluationIdentity {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    (vertexFiber (leftUnstraighteningProjection (presheafInfinityEvaluation y))
      (functorVertex (representablePresheafInfinity y))) _⦋0⦌ :=
  (yonedaEvaluationFiberIso y (representablePresheafInfinity y)).inv.app (Opposite.op ⦋0⦌)
    (canonicalYonedaPointedIdentity y)

/-- 元の fiber 同型は始点を同じ全体からの恒等点へ厳密に戻す。 -/
lemma yonedaEvaluationIdentity_pointed {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    (yonedaEvaluationFiberIso y (representablePresheafInfinity y)).hom.app (Opposite.op ⦋0⦌)
      (yonedaEvaluationIdentity y) = canonicalYonedaPointedIdentity y := by
  let e := ((CategoryTheory.evaluation SimplexCategoryᵒᵖ (Type (u + 1))).obj
    (Opposite.op ⦋0⦌)).mapIso (yonedaEvaluationFiberIso y (representablePresheafInfinity y))
  exact (CategoryTheory.Iso.toEquiv e).apply_symm_apply (canonicalYonedaPointedIdentity y)

/-- 始点の元の全空間射影は、元の Yoneda 対象そのもの。 -/
lemma yonedaEvaluationIdentity_projection {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    (leftUnstraighteningProjection (presheafInfinityEvaluation y)).app (Opposite.op ⦋0⦌)
      (yonedaEvaluationIdentity y).val = functorVertex (representablePresheafInfinity y) := by
  simpa only [PinchedHom.constant_zero] using (yonedaEvaluationIdentity y).property

/-- 全ての前層と全高次にまたがる、同じ恒等点からの元の coslice の比較射。 -/
def yonedaEvaluationCosliceMap {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    sliceUnder (SSet.yonedaEquiv.symm (functorVertex (representablePresheafInfinity y))) ⟶
      leftUnstraightening (presheafInfinityEvaluation y) :=
  cosliceUniversalPrismLiftEndpoint (leftUnstraighteningProjection (presheafInfinityEvaluation y))
    (functorVertex (representablePresheafInfinity y)) (yonedaEvaluationIdentity y).val
    (yonedaEvaluationIdentity_projection y)

/-- 元の比較は、元の前層 ∞ 圏への射影を厳密に保つ。 -/
lemma yonedaEvaluationCosliceMap_projection {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    yonedaEvaluationCosliceMap y ≫ leftUnstraighteningProjection (presheafInfinityEvaluation y) =
      sliceUnderProjection
        (SSet.yonedaEquiv.symm (functorVertex (representablePresheafInfinity y))) :=
  cosliceUniversalPrismLiftEndpoint_projection _ _ _ _

/-- 元の恒等錐は、指定した元の恒等点へ厳密に写る。 -/
lemma yonedaEvaluationCosliceMap_identity {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    (yonedaEvaluationCosliceMap y).app (Opposite.op ⦋0⦌)
      (cosliceIdentityCone (functorVertex (representablePresheafInfinity y))) =
        (yonedaEvaluationIdentity y).val :=
  cosliceUniversalPrismLiftEndpoint_identity _ _ _ _

/-- 同じ一つの大域比較を、元の任意の前層への実際の写像空間に制限した射。 -/
def yonedaEvaluationCosliceFiber {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) :
    vertexFiber (sliceUnderProjection
      (SSet.yonedaEquiv.symm (functorVertex (representablePresheafInfinity y))))
      (functorVertex F) ⟶
    vertexFiber pointedSpaceProjection (F.app _ (ULift.up (SSet.opObjEquiv.symm y))) :=
  vertexFiberMap _ _ (yonedaEvaluationCosliceMap y) (yonedaEvaluationCosliceMap_projection y)
    (functorVertex F) ≫ (yonedaEvaluationFiberIso y F).hom

end SerrePositivity.InfinityCategories.F2.Compact
