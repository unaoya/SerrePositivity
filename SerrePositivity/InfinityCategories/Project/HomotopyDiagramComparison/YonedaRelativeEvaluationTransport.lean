module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.RelativeEvaluationTransport
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.YonedaRelativeCompositionEvaluation

/-!
概要：元の Yoneda 恒等点評価の底方向の自然性。
方針：元の表現可能 unstraightening の恒等点を全相対評価の輸送比較へ代入する。
規約：同じ恒等点と全相対 Hom を保持し、点ごとの比較の自然性を仮定しない。
使われ方：元の有限余積の脚の両側を、同じ評価点の輸送へ比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の恒等点を先に輸送した全評価は、元の恒等点評価後の輸送と全族で同型。 -/
def canonicalYonedaRelativeEvaluation_transportIso
    {E C : SSet.{u}} [Quasicategory C] (p : E ⟶ C.op) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (x y : C _⦋0⦌) (e : SSet.Edge (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.canonicalYonedaIdentityFiber y))
          (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p
            (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y)))) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport
            (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y)) e ▷
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p
            (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorFiberEvaluation
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y)) p
          (SSet.opObjEquiv.symm x))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CanonicalYonedaUnstraighteningIdentity.canonicalYonedaUnstraighteningEvaluation p y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e) := by
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y)
  let j := lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.canonicalYonedaIdentityFiber y)) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p q))
  have he : j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorFiberEvaluation q p (SSet.opObjEquiv.symm y) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CanonicalYonedaUnstraighteningIdentity.canonicalYonedaUnstraighteningEvaluation p y := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.canonicalYonedaUnstraighteningEvaluation_eq_fiberEvaluation]
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeFunctorFiberEvaluation_point q p _ (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.canonicalYonedaIdentityFiber y)
  have h := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeFunctorEvaluation_transportIso q p e).precomp j
  simpa only [← Category.assoc, he] using h

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
