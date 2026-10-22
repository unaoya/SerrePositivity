module

public import SerrePositivity.InfinityCategories.F2.Compact.YonedaEvaluationTransport
public import SerrePositivity.InfinityCategories.F1.LeftFibrationFiberComparison

/-!
概要：元の Yoneda coslice と元の前層評価の全空間の大域比較は、底上の同値。
方針：同じ恒等点からの輸送を既存の全 Yoneda 評価へ同定し、各 fiber の同値を検出。
規約：対象ごとの逆を選ばず、構成した一つの元の比較射の同値性を証明する。
使われ方：元の全共変 Hom 関手と評価の分類図式の全自然同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 固定した始点からの対角輸送は、元の全普遍輸送を同じ点で評価した射。 -/
lemma diagonalFiberTransport_const {E B P : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    {a b : B _⦋0⦌} (z : (vertexFiber p a) _⦋0⦌) (c : P ⟶ intervalMappingSpace a b) :
    diagonalFiberTransport p (SSet.const z) c =
      c ≫ parametrizedFiberTransport p a b ≫ evaluateFunctorAt z := by
  rw [diagonalFiberTransport_evaluate]
  rfl

/-- 同じ大域比較の fiber 作用は、元の coslice 区間比較の後の元の全 Yoneda 評価。 -/
def yonedaEvaluationCosliceFiber_evaluationIso {C : SSet.{u}} [Quasicategory C]
    (y : C _⦋0⦌)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) :
    FunctorIso (yonedaEvaluationCosliceFiber y F)
      (cosliceFiberToIntervalMappingSpace (functorVertex (representablePresheafInfinity y))
        (functorVertex F) ≫ canonicalYonedaTransformationFiberEvaluation y F) := by
  have h := yonedaEvaluationCosliceFiber_pointedTransportIso y F
  rw [diagonalFiberTransport_const] at h
  have e := FunctorIso.precomp (canonicalYonedaTransformationFiberEvaluation_parametrizedIso y F)
    (cosliceFiberToIntervalMappingSpace
      (functorVertex (representablePresheafInfinity y)) (functorVertex F))
  exact h ≪≫ (by simpa only [presheafInfinityEvaluation, Category.assoc] using e.symm)

/-- 元の一つの大域比較は、任意の前層での同じ元の fiber 比較として同値。 -/
lemma yonedaEvaluationCosliceFiber_isQCatEquivalence {C : SSet.{u}} [Quasicategory C]
    (y : C _⦋0⦌)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) :
    IsQCatEquivalence (yonedaEvaluationCosliceFiber y F) :=
  ((cosliceFiberToIntervalMappingSpace_isQCatEquivalence _ _).comp
    (canonicalYonedaTransformationFiberEvaluation_isQCatEquivalence y F)).ofFunctorIso
      (yonedaEvaluationCosliceFiber_evaluationIso y F).symm

/-- 全 fiber の実際の比較から、元の底上の大域比較自身の前合成同値性が従う。 -/
lemma yonedaEvaluationCosliceMap_isPrecompositionEquivalence {C : SSet.{u}} [Quasicategory C]
    (y : C _⦋0⦌) : IsPrecompositionEquivalence (yonedaEvaluationCosliceMap y) := by
  apply isPrecompositionEquivalence_of_leftFibration_fibers
    (sliceUnderProjection
      (SSet.yonedaEquiv.symm (functorVertex (representablePresheafInfinity y))))
    (leftUnstraighteningProjection (presheafInfinityEvaluation y))
    (yonedaEvaluationCosliceMap y) (yonedaEvaluationCosliceMap_projection y)
  intro b
  obtain ⟨F, rfl⟩ := (functorVertexEquiv _ _).surjective b
  simp only [functorVertexEquiv_apply]
  exact (qCatEquivalenceOfIso (yonedaEvaluationFiberIso y F)).isQCatEquivalence.cancel_right
    (yonedaEvaluationCosliceFiber_isQCatEquivalence y F)

end SerrePositivity.InfinityCategories.F2.Compact
