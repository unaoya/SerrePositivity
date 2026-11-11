module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LocalNativeRestrictionGlobalFactors
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IteratedLocalRestrictionGlobalEndpoints

/-!
概要：元の全 Hom 上で回収した結合比較と制限自然性は、同じ中間作用で貼り合う。
方針：元の二因子の厳密な共通端点から指定因子の端点をそろえる。
規約：既存の局所自然性と全 Hom 作用の指定値を保持する。
使われ方：既存の nativeRestrictionIso 全体と元の大域三角形の照合。

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

/-- 元の二因子が共有する同じ中間作用は、大域上で回収した指定因子の端点もそろえる。 -/
lemma cocartesianLocalNativeRestrictionGlobal_middle :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeGlobalSecondNaturalityPostIso l k p q).sourceMap =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeGlobalNativeTransportPostIso l k p q).targetMap := by
  have hs := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIteratedLocalHomComparison_restrictionIso_originalHom_endpoints
    l k p q).1
  have ht := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianLocalNativeRestrictionNativeFactor_originalHom_endpoints l k p q).2
  exact hs.symm.trans ht

/-- 元の共通端点へ始点だけをそろえた、同じ指定制限自然性。 -/
def cocartesianBaseChangeGlobalRestrictionComparisonNormalizedIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeGlobalNativeTransportPostIso l k p q).targetMap
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeFirstGlobalRestrictionNormalizedIso l k p q).sourceMap :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeGlobalRestrictionComparisonIso l k p q)
    (cocartesianLocalNativeRestrictionGlobal_middle l k p q) rfl

/-- 元の全 Hom 上の既存の局所自然性を表す、同じ指定二因子の合成。 -/
def cocartesianBaseChangeGlobalNativeRestrictionComparisonIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeGlobalTransportCompositionIso l k p q).targetMap
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeFirstGlobalRestrictionNormalizedIso l k p q).sourceMap :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeGlobalNativeComparisonIso l k p q ≪≫
    cocartesianBaseChangeGlobalRestrictionComparisonNormalizedIso l k p q

/-- 中間作用をそろえた後も、既存の局所制限自然性の元の全 Hom 上の指定値を保つ。 -/
lemma cocartesianBaseChangeGlobalRestrictionComparisonNormalizedIso_originalHom_heq :
    HEq (cocartesianBaseChangeGlobalRestrictionComparisonNormalizedIso l k p q)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIteratedLocalHomComparison_restrictionIso l k p q).precomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSingleBaseChangeHomAction k p q)) := by
  exact HEq.trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIteratedLocalHomComparison_restrictionIso_originalHom_heq l k p q).symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
