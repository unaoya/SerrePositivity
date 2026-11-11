module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.YonedaSourceBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.SourceInitial
public import
  SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningInfinityReconstruction
public import
  SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraighteningFunctorIso

/-!
概要：元の Yoneda 写像の評価の小さい復元を、元の左 slice と底上で比較する。
方針：始点固定 twisted arrow の実比較、同じ分類図式の復元、全関手同型の輸送を合成する。
規約：底上の厳密等式と同じ全空間の前合成同値を保持する新規の葉。
使われ方：元の Yoneda 写像による極限保存。既存の深層モジュールは変更しない。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 元の左 slice を、同じ Yoneda 全射の指定評価の小さい unstraightening へ写す。 -/
def yonedaEvaluationCosliceComparison {C : SSet.{u}} [Quasicategory C] (x : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm x) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityEvaluation x) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceToTwistedArrowSource x ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityReconstruction (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceProjection x) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningComparisonOfFunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_evaluation_sourceIso x).symm

/-- 指定比較は元の C の全底を厳密に保つ。 -/
lemma yonedaEvaluationCosliceComparison_projection {C : SSet.{u}} [Quasicategory C]
    (x : C _⦋0⦌) :
    yonedaEvaluationCosliceComparison x ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityEvaluation x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x) := by
  simp only [yonedaEvaluationCosliceComparison, Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningComparisonOfFunctorIso_projection,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityReconstruction_projection,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceToTwistedArrowSource_projection]

/-- 同じ底上の指定比較そのものは、任意の quasicategory への前合成同値。 -/
lemma yonedaEvaluationCosliceComparison_isPrecompositionEquivalence
    {C : SSet.{u}} [Quasicategory C] (x : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (yonedaEvaluationCosliceComparison x) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceToTwistedArrowSource_isPrecompositionEquivalence x).comp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityReconstruction_isPrecompositionEquivalence _).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningComparisonOfFunctorIso_isPrecompositionEquivalence _))

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
