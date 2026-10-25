module

public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaSourceBaseChange
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.SourceInitial
public import
  SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningInfinityReconstruction
public import
  SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningFunctorIso

/-!
概要：元の Yoneda 写像の評価の小さい復元を、元の左 slice と底上で比較する。
方針：始点固定 twisted arrow の実比較、同じ分類図式の復元、全関手同型の輸送を合成する。
規約：底上の厳密等式と同じ全空間の前合成同値を保持する新規の葉。
使われ方：元の Yoneda 写像による極限保存。既存の深層モジュールは変更しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の左 slice を、同じ Yoneda 全射の指定評価の小さい unstraightening へ写す。 -/
def yonedaEvaluationCosliceComparison {C : SSet.{u}} [Quasicategory C] (x : C _⦋0⦌) :
    sliceUnder (SSet.yonedaEquiv.symm x) ⟶
      smallLeftUnstraightening (yonedaInfinityMap C ≫ presheafInfinityEvaluation x) :=
  cosliceToTwistedArrowSource x ≫
    leftStraighteningInfinityReconstruction (twistedArrowSourceProjection x) ≫
    smallLeftUnstraighteningComparisonOfFunctorIso (yonedaInfinityMap_evaluation_sourceIso x).symm

/-- 指定比較は元の C の全底を厳密に保つ。 -/
lemma yonedaEvaluationCosliceComparison_projection {C : SSet.{u}} [Quasicategory C]
    (x : C _⦋0⦌) :
    yonedaEvaluationCosliceComparison x ≫
        smallLeftUnstraighteningProjection (yonedaInfinityMap C ≫ presheafInfinityEvaluation x) =
      sliceUnderProjection (SSet.yonedaEquiv.symm x) := by
  simp only [yonedaEvaluationCosliceComparison, Category.assoc]
  rw [smallLeftUnstraighteningComparisonOfFunctorIso_projection,
    leftStraighteningInfinityReconstruction_projection,
    cosliceToTwistedArrowSource_projection]

/-- 同じ底上の指定比較そのものは、任意の quasicategory への前合成同値。 -/
lemma yonedaEvaluationCosliceComparison_isPrecompositionEquivalence
    {C : SSet.{u}} [Quasicategory C] (x : C _⦋0⦌) :
    IsPrecompositionEquivalence (yonedaEvaluationCosliceComparison x) :=
  (cosliceToTwistedArrowSource_isPrecompositionEquivalence x).comp
    ((leftStraighteningInfinityReconstruction_isPrecompositionEquivalence _).comp
      (smallLeftUnstraighteningComparisonOfFunctorIso_isPrecompositionEquivalence _))

end SerrePositivity.InfinityCategories
