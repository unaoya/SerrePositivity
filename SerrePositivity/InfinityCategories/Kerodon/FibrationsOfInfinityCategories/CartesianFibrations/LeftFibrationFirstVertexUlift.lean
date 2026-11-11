module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorPullbackComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.UnstraighteningPullbackEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningInfinityReconstruction

/-!
概要：一般の小さい left fibration 対の、持ち上げた初頂点引き戻しの相対 Hom 作用は同値。
方針：元の対の相対表現への比較に、引き戻しの自然性による反映を適用する。
規約：元の底は quasicategory。実際の引き戻しの作用を持ち上げた宇宙で比較する。
使われ方：一般の straightening の充満忠実性を、元の宇宙へ反映する直前の段階。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 元の二つの left fibrations を持ち上げた初頂点引き戻しは、実際の相対 Hom 上で同値。 -/
lemma leftFibrationFirstVertexUliftPullback_isQCatEquivalence
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPullback
      ((SSet.uliftFunctor.{u + 1, u}).map p)
      ((SSet.uliftFunctor.{u + 1, u}).map q)
      ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B))) := by
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.nativeLeftTransportRepresentation p
  let Q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.nativeLeftTransportRepresentation q
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorPullback_isQCatEquivalence_of_comparison
    ((SSet.uliftFunctor.{u + 1, u}).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection P.diagram)
    ((SSet.uliftFunctor.{u + 1, u}).map q) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection Q.diagram)
    P.comparison P.over_base P.isPrecompositionEquivalence
    Q.comparison Q.over_base Q.isPrecompositionEquivalence _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningFirstVertexPullback_isQCatEquivalence B P.diagram Q.diagram)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
