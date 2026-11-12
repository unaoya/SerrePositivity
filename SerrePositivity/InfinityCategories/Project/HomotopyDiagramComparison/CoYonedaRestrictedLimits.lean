module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoYonedaConeLimits

/-!
概要：元の全 co-Yoneda 族を係数関手で制限しても、同じ全極限錐を保存する。
方針：各評価を元の係数関手の像での評価へ厳密に同定する。
規約：点ごとの存在ではなく元の指定全錐を保存する。
使われ方：P_Σ の全 Hom 係数族の極限保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 概要：全 co-Yoneda 族の同じ係数制限は、元の全極限錐を極限へ送る。
方針：全評価の可換性で元の co-Yoneda の点ごとの極限性を適用する。
規約：係数関手の充満忠実性や始域の充填性は要求しない。
使われ方：全 Hom 族を元の延長の標的係数へ制限する。 -/
lemma coyonedaInfinityMap_restricted_isLimit {K A Y : SSet.{u}} [Quasicategory Y]
    (F : A ⟶ Y) {p : K ⟶ Y.op} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap Y ≫
      (pre ((SSet.uliftFunctor.{u + 1, u}).map F)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_of_pointwise
  rintro ⟨a⟩
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coyonedaInfinityMap_isPointwiseLimit c hc (ULift.up (F.app _ a))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap Y ≫
      (pre ((SSet.uliftFunctor.{u + 1, u}).map F)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up a)) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c))
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.evaluateFunctorAt_pre]
  exact h

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
