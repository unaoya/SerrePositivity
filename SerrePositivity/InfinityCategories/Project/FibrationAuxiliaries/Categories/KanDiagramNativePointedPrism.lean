module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.KanDiagramNativeLeftIntervalEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedKanParameterizedPrism

/-!
概要：native な左区間の対象評価に沿う、両端を指定した実際の pointed prism を構成する。
方針：元の strict 変換の評価の prism を共通 Hom の右端で制限し、底の厳密な式を使う。
規約：これは各対象の全パラメーターでの構成であり、weighted 始域上への貼り合わせは別課題。
使われ方：分類写像の実際の全 Hom 作用と weighted 比較の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories


/-- 各対象で、同じ native 区間上に元の変換の評価を終点とする pointed prism を作る。 -/
def kanDiagramNativePointedTransportFamily
    {I : Type u} [SmallCategory I] (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) (i : I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily
      (b := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj (G.val.obj i)))
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedSpaceLeftResolutionComparison (F.val.obj i))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramOppositeLeftHomInterval F G) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i))) := by
  let f := uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent
    (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) i)
  let T := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedKanParameterizedTransportFamily
    (X := F.val.obj i) (Y := G.val.obj i) f).precomp
      ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight (SimplicialCategory.sHom F G)))
  have hBase : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramOppositeLeftHomInterval F G) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)) =
      (Δ[1] ◁ (SSet.uliftFunctor.{u + 1, u}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight (SimplicialCategory.sHom F G))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanParameterizedLeftHomInterval
        (X := F.val.obj i) (Y := G.val.obj i) f) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramOppositeLeftHomInterval_evaluate_action,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanParameterizedLeftHomInterval, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_curryOfEndpoints, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedReverseKanHomInterval_eq_left]
    simp only [whiskerLeft_comp, Category.assoc]
    rfl
  refine
    { endpoint := T.endpoint
      prism := T.prism
      start := T.start
      finish := T.finish
      over_base := ?_ }
  rw [hBase]
  exact T.over_base

/-- 同じ共通 Hom の右端を使った元の strict 変換の評価が prism の実際の終点。 -/
lemma kanDiagramNativePointedTransportFamily_endpoint
    {I : Type u} [SmallCategory I] (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) (i : I) :
    (kanDiagramNativePointedTransportFamily F G i).endpoint =
      ((SSet.uliftFunctor.{u + 1, u}).obj (F.val.obj i).obj ◁
        (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight (SimplicialCategory.sHom F G))) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso (F.val.obj i).obj (SimplicialCategory.sHom F G)).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent
        (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) i)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedSpaceLeftResolutionComparison (G.val.obj i) := rfl

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
