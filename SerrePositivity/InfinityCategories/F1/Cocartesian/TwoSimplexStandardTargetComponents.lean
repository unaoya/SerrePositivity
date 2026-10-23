module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexStandardOverNaturality
public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexLocalComparison
public import SerrePositivity.InfinityCategories.F1.IntervalDiagramOverIsomorphism

/-!
概要：元の target cospan の三成分を、同じ標準セルへの制限同型で移す。
方針：同じ底上の同型に元の区間 Hom の反変制限を作用させる。
規約：元の分類図式と二辺・共有頂点を保持する。
使われ方：元の target 制限を標準内ホーンへの制限へ照合する。
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
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom

/-- 元の最初の辺の Hom を同じ標準セルへ制限する同型の射。 -/
def cocartesianTwoSimplexStandardTargetFirstMap :=
  intervalDiagramOverPre
    (cocartesianStrictTransportCoherentDiagram p.val.hom)
    (cocartesianStrictTransportCoherentDiagram q.val.hom)
    (cocartesianTwoSimplexStandardFirstOverIso k).hom

/-- 元の次の辺の Hom を同じ標準セルへ制限する同型の射。 -/
def cocartesianTwoSimplexStandardTargetSecondMap :=
  intervalDiagramOverPre
    (cocartesianStrictTransportCoherentDiagram p.val.hom)
    (cocartesianStrictTransportCoherentDiagram q.val.hom)
    (cocartesianTwoSimplexStandardSecondOverIso k).hom

/-- 元の共有頂点の Hom を同じ標準セルへ制限する同型の射。 -/
def cocartesianTwoSimplexStandardTargetSharedMap :=
  intervalDiagramOverPre
    (cocartesianStrictTransportCoherentDiagram p.val.hom)
    (cocartesianStrictTransportCoherentDiagram q.val.hom)
    (cocartesianTwoSimplexStandardSharedOverIso k).hom

/-- 同じ標準セルへの制限は、最初の脚に沿って厳密に自然。 -/
lemma cocartesianTwoSimplexStandardTargetFirstMap_naturality :
    cocartesianTwoSimplexStandardTargetFirstMap k p q ≫
      intervalDiagramOverPre
        (cocartesianStrictTransportCoherentDiagram p.val.hom)
        (cocartesianStrictTransportCoherentDiagram q.val.hom)
        (InnerTwoHornOver.toFirst (cocartesianTwoSimplexStandardHorn k)) =
    (cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inl ≫
      cocartesianTwoSimplexStandardTargetSharedMap k p q := by
  exact (intervalDiagramOverPre_comp P Q
    (InnerTwoHornOver.toFirst (cocartesianTwoSimplexStandardHorn k))
    (cocartesianTwoSimplexStandardFirstOverIso k).hom).trans
    ((congrArg (intervalDiagramOverPre P Q)
      (cocartesianTwoSimplexStandardOverIso_first k).symm).trans
      (intervalDiagramOverPre_comp P Q (cocartesianTwoSimplexStandardSharedOverIso k).hom
        (uliftOverMorphism (cocartesianTwoSimplexSharedToFirst k))).symm)

/-- 同じ標準セルへの制限は、次の脚に沿って厳密に自然。 -/
lemma cocartesianTwoSimplexStandardTargetSecondMap_naturality :
    cocartesianTwoSimplexStandardTargetSecondMap k p q ≫
      intervalDiagramOverPre
        (cocartesianStrictTransportCoherentDiagram p.val.hom)
        (cocartesianStrictTransportCoherentDiagram q.val.hom)
        (InnerTwoHornOver.toSecond (cocartesianTwoSimplexStandardHorn k)) =
    (cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inr ≫
      cocartesianTwoSimplexStandardTargetSharedMap k p q := by
  exact (intervalDiagramOverPre_comp P Q
    (InnerTwoHornOver.toSecond (cocartesianTwoSimplexStandardHorn k))
    (cocartesianTwoSimplexStandardSecondOverIso k).hom).trans
    ((congrArg (intervalDiagramOverPre P Q)
      (cocartesianTwoSimplexStandardOverIso_second k).symm).trans
      (intervalDiagramOverPre_comp P Q (cocartesianTwoSimplexStandardSharedOverIso k).hom
        (uliftOverMorphism (cocartesianTwoSimplexSharedToSecond k))).symm)

end SerrePositivity.InfinityCategories
