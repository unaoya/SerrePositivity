module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldSmallOverIsos
public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldLocalComparison
public import SerrePositivity.InfinityCategories.F1.Cocartesian.PullbackNativeLiftRestriction

/-!
概要：元の source cospan の三成分を、同じ小さい標準セルへの制限同型で移す。
方針：元の native core の制限の関手性と底上の同じ表示同型を使う。
規約：元の全局所 Hom と最初の辺と尾部・共有頂点を保持する。
使われ方：元の source 制限と同じ貼合せ制限の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))
local notation "P" => p.val.hom
local notation "Q" => q.val.hom
local notation "H" => cocartesianScaffoldSmallBridge n k

/-- 元の最初の辺の native core を同じ小さい標準セルへ制限する射。 -/
def cocartesianScaffoldStandardSourceFirstMap :=
  cocartesianPullbackNativeLiftPre P Q (cocartesianScaffoldSmallFirstOverIso n k).hom

/-- 元の次の辺の native core を同じ小さい標準セルへ制限する射。 -/
def cocartesianScaffoldStandardSourceSecondMap :=
  cocartesianPullbackNativeLiftPre P Q (cocartesianScaffoldSmallTailOverIso n k).hom

/-- 元の共有頂点の native core を同じ小さい標準セルへ制限する射。 -/
def cocartesianScaffoldStandardSourceSharedMap :=
  cocartesianPullbackNativeLiftPre P Q (cocartesianScaffoldSmallSharedOverIso n k).hom

/-- 同じ元の source 制限は、最初の標準セルの脚に沿って厳密に自然。 -/
lemma cocartesianScaffoldStandardSourceFirstMap_naturality :
    cocartesianScaffoldStandardSourceFirstMap n k p q ≫
      cocartesianPullbackNativeLiftPre P Q (ScaffoldBridgeOver.toFirst n H) =
    (cocartesianScaffoldLocalSource n k p q).map WalkingCospan.Hom.inl ≫
      cocartesianScaffoldStandardSourceSharedMap n k p q := by
  exact (cocartesianPullbackNativeLiftPre_comp P Q (ScaffoldBridgeOver.toFirst n H)
    (cocartesianScaffoldSmallFirstOverIso n k).hom).trans
    ((congrArg (cocartesianPullbackNativeLiftPre P Q)
      (cocartesianScaffoldSmallOverIso_first n k).symm).trans
      (cocartesianPullbackNativeLiftPre_comp P Q
        (cocartesianScaffoldSmallSharedOverIso n k).hom
        (cocartesianScaffoldSharedToFirst n k)).symm)

/-- 同じ元の source 制限は、次の標準セルの脚に沿って厳密に自然。 -/
lemma cocartesianScaffoldStandardSourceSecondMap_naturality :
    cocartesianScaffoldStandardSourceSecondMap n k p q ≫
      cocartesianPullbackNativeLiftPre P Q (ScaffoldBridgeOver.toTail n H) =
    (cocartesianScaffoldLocalSource n k p q).map WalkingCospan.Hom.inr ≫
      cocartesianScaffoldStandardSourceSharedMap n k p q := by
  exact (cocartesianPullbackNativeLiftPre_comp P Q (ScaffoldBridgeOver.toTail n H)
    (cocartesianScaffoldSmallTailOverIso n k).hom).trans
    ((congrArg (cocartesianPullbackNativeLiftPre P Q)
      (cocartesianScaffoldSmallOverIso_tail n k).symm).trans
      (cocartesianPullbackNativeLiftPre_comp P Q
        (cocartesianScaffoldSmallSharedOverIso n k).hom
        (cocartesianScaffoldSharedToTail n k)).symm)

end SerrePositivity.InfinityCategories
