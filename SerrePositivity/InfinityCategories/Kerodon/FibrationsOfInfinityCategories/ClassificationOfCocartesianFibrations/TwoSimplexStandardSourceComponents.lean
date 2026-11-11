module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoSimplexSmallStandardOverNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoSimplexLocalComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PullbackNativeLiftRestriction

/-!
概要：元の source cospan の三成分を、同じ小さい標準セルへの制限同型で移す。
方針：元の native core の制限の関手性と底上の同じ表示同型を使う。
規約：元の全局所 Hom と二辺・共有頂点を保持する。
使われ方：元の source 制限と標準内ホーン制限の照合。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 3) ⥤ C)
  (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))
local notation "P" => p.val.hom
local notation "Q" => q.val.hom
local notation "H" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexSmallStandardHorn k

/-- 元の最初の辺の native core を同じ小さい標準セルへ制限する射。 -/
def cocartesianTwoSimplexStandardSourceFirstMap :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre P Q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexSmallStandardFirstOverIso k).hom

/-- 元の次の辺の native core を同じ小さい標準セルへ制限する射。 -/
def cocartesianTwoSimplexStandardSourceSecondMap :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre P Q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexSmallStandardSecondOverIso k).hom

/-- 元の共有頂点の native core を同じ小さい標準セルへ制限する射。 -/
def cocartesianTwoSimplexStandardSourceSharedMap :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre P Q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexSmallStandardSharedOverIso k).hom

/-- 同じ元の source 制限は、最初の標準セルの脚に沿って厳密に自然。 -/
lemma cocartesianTwoSimplexStandardSourceFirstMap_naturality :
    cocartesianTwoSimplexStandardSourceFirstMap k p q ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre P Q (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.InnerTwoHornOver.toFirst H) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexLocalSource k p q).map WalkingCospan.Hom.inl ≫
      cocartesianTwoSimplexStandardSourceSharedMap k p q := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre_comp P Q (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.InnerTwoHornOver.toFirst H)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexSmallStandardFirstOverIso k).hom).trans
    ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre P Q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexSmallStandardOverIso_first k).symm).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre_comp P Q
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexSmallStandardSharedOverIso k).hom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexSharedToFirst k)).symm)

/-- 同じ元の source 制限は、次の標準セルの脚に沿って厳密に自然。 -/
lemma cocartesianTwoSimplexStandardSourceSecondMap_naturality :
    cocartesianTwoSimplexStandardSourceSecondMap k p q ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre P Q (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.InnerTwoHornOver.toSecond H) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexLocalSource k p q).map WalkingCospan.Hom.inr ≫
      cocartesianTwoSimplexStandardSourceSharedMap k p q := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre_comp P Q (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.InnerTwoHornOver.toSecond H)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexSmallStandardSecondOverIso k).hom).trans
    ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre P Q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexSmallStandardOverIso_second k).symm).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre_comp P Q
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexSmallStandardSharedOverIso k).hom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexSharedToSecond k)).symm)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
