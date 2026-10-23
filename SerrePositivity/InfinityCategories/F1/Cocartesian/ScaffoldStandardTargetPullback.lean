module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldStandardTargetComponents
public import SerrePositivity.InfinityCategories.F1.SpanPullbackIsomorphism
public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldTargetSegal

/-!
概要：元の target pullback と同じ同じ貼合せの target pullback を同型で結ぶ。
方針：底上の同じ三つの表示同型を、元の区間 Hom の pullback へ作用させる。
規約：元の最初の辺と尾部と同じ共有頂点を保持する。
使われ方：恒等高次単体の target 制限の自明 Kan 性の移送。
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
local notation "H" => cocartesianScaffoldLargeBridge n k
local notation "T" => cocartesianScaffoldLocalTarget n k p q

/-- 元の target pullback から同じ標準セルの target pullback への表示比較。 -/
def cocartesianScaffoldStandardTargetPullbackMap :
    pullback ((T).map WalkingCospan.Hom.inl) ((T).map WalkingCospan.Hom.inr) ⟶
      pullback (intervalDiagramOverPre P Q (ScaffoldBridgeOver.toFirst n H))
        (intervalDiagramOverPre P Q (ScaffoldBridgeOver.toTail n H)) :=
  spanPullbackMap _ _ _ _ (cocartesianScaffoldStandardTargetSharedMap n k p q)
    (cocartesianScaffoldStandardTargetFirstMap n k p q)
    (cocartesianScaffoldStandardTargetSecondMap n k p q)
    (cocartesianScaffoldStandardTargetFirstMap_naturality n k p q)
    (cocartesianScaffoldStandardTargetSecondMap_naturality n k p q)

/-- 三つの表示比較が同型なので、同じ target pullback の表示比較も同型。 -/
lemma cocartesianScaffoldStandardTargetPullbackMap_isIso :
    IsIso (cocartesianScaffoldStandardTargetPullbackMap n k p q) := by
  have : IsIso (cocartesianScaffoldStandardTargetSharedMap n k p q) :=
    intervalDiagramOverPre_isIso_of_isIso P Q
      (cocartesianScaffoldLargeSharedOverIso n k).hom
  have : IsIso (cocartesianScaffoldStandardTargetFirstMap n k p q) :=
    intervalDiagramOverPre_isIso_of_isIso P Q
      (cocartesianScaffoldLargeFirstOverIso n k).hom
  have : IsIso (cocartesianScaffoldStandardTargetSecondMap n k p q) :=
    intervalDiagramOverPre_isIso_of_isIso P Q
      (cocartesianScaffoldLargeTailOverIso n k).hom
  exact spanPullbackMap_isIso _ _ _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories
