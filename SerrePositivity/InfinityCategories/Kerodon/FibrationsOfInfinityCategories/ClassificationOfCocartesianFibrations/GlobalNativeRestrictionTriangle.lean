module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LocalNativeRestrictionGlobalCoherence
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsoTriangleIdentity

/-!
概要：元の全 Hom 上で回収した既存の局所自然性は、元の大域自然性の三角等式を満たす。
方針：同じ指定因子の三辺の等式を、端点をそろえた同じ二因子の合成へまとめる。
規約：元の全 Hom・局所自然性・大域自然性の指定値を保持する。
使われ方：底上の局所自然性と同じ元の大域分類作用の整合性。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))

/-- 元の全 Hom 上の既存の局所自然性は、元の大域自然性と同じ三角形を閉じる。 -/
def CocartesianGlobalNativeRestrictionTriangleCommutes : Prop :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsoTriangleCommutes
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeGlobalNativeRestrictionComparisonIso l k p q)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomNaturalityIso k p q).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomRestrictionZero l k p q))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeGlobalTransportDirectIso l k p q)

/-- 同じ指定二因子をまとめた局所自然性の三角等式を回収する。 -/
lemma cocartesianGlobalNativeRestrictionTriangleCommutes :
    CocartesianGlobalNativeRestrictionTriangleCommutes l k p q := by
  have h₀ : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsoLocalTriangleCommutes
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeGlobalNativeComparisonIso l k p q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeGlobalRestrictionComparisonIso l k p q)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomNaturalityIso k p q).postcomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomRestrictionZero l k p q))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeGlobalTransportDirectIso l k p q) := by
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeGlobalLocalTriangleCommutes l k p q
  have h₁ := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsoLocalTriangleCommutes.replace_second h₀
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeGlobalRestrictionComparisonNormalizedIso l k p q)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _)
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsoLocalTriangleCommutes.merge h₁

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
