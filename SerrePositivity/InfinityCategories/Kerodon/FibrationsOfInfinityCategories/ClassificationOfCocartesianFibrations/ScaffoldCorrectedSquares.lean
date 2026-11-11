module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldLocalPathLifting
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedFunctorSquare

/-!
概要：元の局所 cospan の二つの自然性を、指定 path を保って厳密可換にする。
方針：元の共有頂点成分を固定し、標的の両脚の相対 path 持ち上げを使う。
規約：元の辺成分への path と、元の自然性を表す標的 path を保存する。
使われ方：同じ三成分の同値による厳密な pullback 比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
  (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))

/-- 同じ共有頂点成分を保った最初の脚の、元の自然性 path を持ち上げる厳密化。 -/
def cocartesianScaffoldCorrectedFirstSquare :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedFunctorSquare
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inl)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLocalComparison n k p q WalkingCospan.left)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLocalSource n k p q).map WalkingCospan.Hom.inl ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLocalComparison n k p q WalkingCospan.one)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLocalComparison_firstIso n k p q) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.pathCorrectedFunctorSquare _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLocalTarget_first_kanEquivalenceLifting n k p q) _ _ _

/-- 同じ共有頂点成分を保った次の脚の、元の自然性 path を持ち上げる厳密化。 -/
def cocartesianScaffoldCorrectedSecondSquare :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedFunctorSquare
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inr)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLocalComparison n k p q WalkingCospan.right)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLocalSource n k p q).map WalkingCospan.Hom.inr ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLocalComparison n k p q WalkingCospan.one)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLocalComparison_secondIso n k p q) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.pathCorrectedFunctorSquare _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLocalTarget_second_kanEquivalenceLifting n k p q) _ _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
