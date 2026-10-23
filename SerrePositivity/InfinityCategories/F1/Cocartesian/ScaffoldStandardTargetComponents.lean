module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldLargeOverIsos
public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldLocalComparison
public import SerrePositivity.InfinityCategories.F1.IntervalDiagramOverIsomorphism

/-!
概要：元の target cospan の三成分を、同じ標準セルへの制限同型で移す。
方針：同じ底上の同型に元の区間 Hom の反変制限を作用させる。
規約：元の分類図式と最初の辺と尾部・共有頂点を保持する。
使われ方：元の target 制限を同じ貼合せへの制限へ照合する。
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
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom

/-- 元の最初の辺の Hom を同じ標準セルへ制限する同型の射。 -/
def cocartesianScaffoldStandardTargetFirstMap :=
  intervalDiagramOverPre
    (cocartesianStrictTransportCoherentDiagram p.val.hom)
    (cocartesianStrictTransportCoherentDiagram q.val.hom)
    (cocartesianScaffoldLargeFirstOverIso n k).hom

/-- 元の次の辺の Hom を同じ標準セルへ制限する同型の射。 -/
def cocartesianScaffoldStandardTargetSecondMap :=
  intervalDiagramOverPre
    (cocartesianStrictTransportCoherentDiagram p.val.hom)
    (cocartesianStrictTransportCoherentDiagram q.val.hom)
    (cocartesianScaffoldLargeTailOverIso n k).hom

/-- 元の共有頂点の Hom を同じ標準セルへ制限する同型の射。 -/
def cocartesianScaffoldStandardTargetSharedMap :=
  intervalDiagramOverPre
    (cocartesianStrictTransportCoherentDiagram p.val.hom)
    (cocartesianStrictTransportCoherentDiagram q.val.hom)
    (cocartesianScaffoldLargeSharedOverIso n k).hom

/-- 同じ標準セルへの制限は、最初の脚に沿って厳密に自然。 -/
lemma cocartesianScaffoldStandardTargetFirstMap_naturality :
    cocartesianScaffoldStandardTargetFirstMap n k p q ≫
      intervalDiagramOverPre
        (cocartesianStrictTransportCoherentDiagram p.val.hom)
        (cocartesianStrictTransportCoherentDiagram q.val.hom)
        (ScaffoldBridgeOver.toFirst n (cocartesianScaffoldLargeBridge n k)) =
    (cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inl ≫
      cocartesianScaffoldStandardTargetSharedMap n k p q := by
  exact (intervalDiagramOverPre_comp P Q
    (ScaffoldBridgeOver.toFirst n (cocartesianScaffoldLargeBridge n k))
    (cocartesianScaffoldLargeFirstOverIso n k).hom).trans
    ((congrArg (intervalDiagramOverPre P Q)
      (cocartesianScaffoldLargeOverIso_first n k)).trans
      (intervalDiagramOverPre_comp P Q (cocartesianScaffoldLargeSharedOverIso n k).hom
        (uliftOverMorphism (cocartesianScaffoldSharedToFirst n k))).symm)

/-- 同じ標準セルへの制限は、次の脚に沿って厳密に自然。 -/
lemma cocartesianScaffoldStandardTargetSecondMap_naturality :
    cocartesianScaffoldStandardTargetSecondMap n k p q ≫
      intervalDiagramOverPre
        (cocartesianStrictTransportCoherentDiagram p.val.hom)
        (cocartesianStrictTransportCoherentDiagram q.val.hom)
        (ScaffoldBridgeOver.toTail n (cocartesianScaffoldLargeBridge n k)) =
    (cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inr ≫
      cocartesianScaffoldStandardTargetSharedMap n k p q := by
  exact (intervalDiagramOverPre_comp P Q
    (ScaffoldBridgeOver.toTail n (cocartesianScaffoldLargeBridge n k))
    (cocartesianScaffoldLargeTailOverIso n k).hom).trans
    ((congrArg (intervalDiagramOverPre P Q)
      (cocartesianScaffoldLargeOverIso_tail n k)).trans
      (intervalDiagramOverPre_comp P Q (cocartesianScaffoldLargeSharedOverIso n k).hom
        (uliftOverMorphism (cocartesianScaffoldSharedToTail n k))).symm)

end SerrePositivity.InfinityCategories
