module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftFibrationPointEvaluation
public import SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.EquivalenceColimits
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningInfinityEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.FunctorPointwiseColimitCriterion
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport

/-!
概要：底上の left fibrations の strict filtered 余極限全余錐は、元の ∞ 圏でも余極限である。
方針：元の分類同値で写し、全頂点の評価を有限な一点始域の相対 Hom と全自然比較する。
規約：元の同じ全余錐を判定する。頂点の存在だけや通常の余極限だけで結論しない。
使われ方：有限底上模型の filtered 全表示の native な普遍性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：元の通常の底上の filtered 全余錐は、left fibration ∞ 圏で余極限である。
方針：分類同値の点ごとの評価を、有限な一点始域の相対 Hom と比較する。
規約：同じ指定余錐の全 join 射を保持する。
使われ方：有限底上模型の全表示の native な普遍性。 -/
lemma leftFibrationStrictCocone_isColimit {B : SSet.{u}} [Quasicategory B]
    {J : Type u} [SmallCategory J] [IsFiltered J] {F : J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B}
    (c : Cocone F) (hc : IsColimit ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftFibrationObjectForget B).mapCocone c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone c) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.equivalence_isColimitCone_iff (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_isQCatEquivalence B)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone c)).mpr
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isColimitCone_of_pointwise
  rintro ⟨b⟩
  let A : Over B := Over.mk (SSet.yonedaEquiv.symm b)
  have : A.left.Finite := inferInstanceAs (Δ[0] : SSet.{u}).Finite
  have hpoint := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteRelativeHom_preserves_strictCocone
    A c hc
  have hfiber : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation b) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone c)) :=
    hpoint.of_functorIso
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftFibrationPointEvaluationIso b).precomp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone c).val)
  have heval : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up b)) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone c)) :=
    hfiber.of_functorIso
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_evaluateIso b).precomp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone c).val).symm
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ (Category.assoc _ _ _).symm).mp heval

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
