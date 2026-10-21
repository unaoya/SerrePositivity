module

public import SerrePositivity.InfinityCategories.F1.CocartesianTwoSimplexSmallStandardOverNaturality
public import SerrePositivity.InfinityCategories.F1.CocartesianTwoSimplexLocalComparison
public import SerrePositivity.InfinityCategories.F1.CocartesianPullbackNativeLiftRestriction

/-!
概要：元の source cospan の三成分を、同じ小さい標準セルへの制限同型で移す。
方針：元の native core の制限の関手性と底上の同じ表示同型を使う。
規約：元の全局所 Hom と二辺・共有頂点を保持する。
使われ方：元の source 制限と標準内ホーン制限の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 3) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))
local notation "P" => p.val.hom
local notation "Q" => q.val.hom
local notation "H" => cocartesianTwoSimplexSmallStandardHorn k

/-- 元の最初の辺の native core を同じ小さい標準セルへ制限する射。 -/
def cocartesianTwoSimplexStandardSourceFirstMap :=
  cocartesianPullbackNativeLiftPre P Q (cocartesianTwoSimplexSmallStandardFirstOverIso k).hom

/-- 元の次の辺の native core を同じ小さい標準セルへ制限する射。 -/
def cocartesianTwoSimplexStandardSourceSecondMap :=
  cocartesianPullbackNativeLiftPre P Q (cocartesianTwoSimplexSmallStandardSecondOverIso k).hom

/-- 元の共有頂点の native core を同じ小さい標準セルへ制限する射。 -/
def cocartesianTwoSimplexStandardSourceSharedMap :=
  cocartesianPullbackNativeLiftPre P Q (cocartesianTwoSimplexSmallStandardSharedOverIso k).hom

/-- 同じ元の source 制限は、最初の標準セルの脚に沿って厳密に自然。 -/
lemma cocartesianTwoSimplexStandardSourceFirstMap_naturality :
    cocartesianTwoSimplexStandardSourceFirstMap k p q ≫
      cocartesianPullbackNativeLiftPre P Q (InnerTwoHornOver.toFirst H) =
    (cocartesianTwoSimplexLocalSource k p q).map WalkingCospan.Hom.inl ≫
      cocartesianTwoSimplexStandardSourceSharedMap k p q := by
  exact (cocartesianPullbackNativeLiftPre_comp P Q (InnerTwoHornOver.toFirst H)
    (cocartesianTwoSimplexSmallStandardFirstOverIso k).hom).trans
    ((congrArg (cocartesianPullbackNativeLiftPre P Q)
      (cocartesianTwoSimplexSmallStandardOverIso_first k).symm).trans
      (cocartesianPullbackNativeLiftPre_comp P Q
        (cocartesianTwoSimplexSmallStandardSharedOverIso k).hom
        (cocartesianTwoSimplexSharedToFirst k)).symm)

/-- 同じ元の source 制限は、次の標準セルの脚に沿って厳密に自然。 -/
lemma cocartesianTwoSimplexStandardSourceSecondMap_naturality :
    cocartesianTwoSimplexStandardSourceSecondMap k p q ≫
      cocartesianPullbackNativeLiftPre P Q (InnerTwoHornOver.toSecond H) =
    (cocartesianTwoSimplexLocalSource k p q).map WalkingCospan.Hom.inr ≫
      cocartesianTwoSimplexStandardSourceSharedMap k p q := by
  exact (cocartesianPullbackNativeLiftPre_comp P Q (InnerTwoHornOver.toSecond H)
    (cocartesianTwoSimplexSmallStandardSecondOverIso k).hom).trans
    ((congrArg (cocartesianPullbackNativeLiftPre P Q)
      (cocartesianTwoSimplexSmallStandardOverIso_second k).symm).trans
      (cocartesianPullbackNativeLiftPre_comp P Q
        (cocartesianTwoSimplexSmallStandardSharedOverIso k).hom
        (cocartesianTwoSimplexSharedToSecond k)).symm)

end SerrePositivity.InfinityCategories
