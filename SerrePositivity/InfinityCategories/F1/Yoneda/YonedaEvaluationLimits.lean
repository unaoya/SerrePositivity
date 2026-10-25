module

public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaEvaluationCoslice
public import SerrePositivity.InfinityCategories.HomotopyLimits.LiftedConePointedRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpacePointLimitDetection
public import SerrePositivity.InfinityCategories.F1.Coherent.SpaceSmallLimits

/-!
概要：元の Yoneda 全射の各評価は、元の任意の小さい全極限錐を保存する。
方針：元の左 slice の切断制限を同じ評価の小さい復元へ移し、一点からの制限で検出する。
規約：有限性・離散性は不要。同じ native 全錐を使い、既存の深層ファイルは変更しない。
使われ方：Yoneda の極限保存と Ind の有限極限を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 元の Yoneda 全射の指定評価は、元の同じ全極限錐の像を極限錐にする。 -/
lemma yonedaInfinityMap_evaluation_isLimit {K C : SSet.{u}} [Quasicategory C]
    {D : K ⟶ C} (c : JoinCone D) (hc : IsLimitCone c) (x : C _⦋0⦌) :
    IsLimitCone (mapJoinCone (yonedaInfinityMap C ≫ presheafInfinityEvaluation x)
      (JoinCone.ulift.{u, u + 1} c)) := by
  let F := yonedaInfinityMap C ≫ presheafInfinityEvaluation x
  apply spaceCone_isLimit_of_pointRestriction_of_hasLimit _
    (hasLimit_coherentSpaceDiagram ((SSet.uliftFunctor.{u + 1, u}).map D ≫ F))
  apply coherentPointedRestriction_nativeCone_isQCatEquivalence c F
  apply coherentPointedRestriction_isQCatEquivalence
  rw [← leftFibrationConeRestriction_eq_overPre]
  apply (leftFibrationConeRestriction_isQCatEquivalence_iff_of_comparison
    (sliceUnderProjection (SSet.yonedaEquiv.symm x))
    (smallLeftUnstraighteningProjection F) (yonedaEvaluationCosliceComparison x)
    (yonedaEvaluationCosliceComparison_projection x)
    (yonedaEvaluationCosliceComparison_isPrecompositionEquivalence x) c).mp
  exact ((isLimitCone_iff_coneSectionRestriction_homotopyEquivalence c).mp hc x).isQCatEquivalence

end SerrePositivity.InfinityCategories
