module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexStandardTargetComponents
public import SerrePositivity.InfinityCategories.F1.Joins.SpanPullbackIsomorphism
public import SerrePositivity.InfinityCategories.F1.Simplicial.InnerTwoHornHomPullbacks

/-!
概要：元の target pullback と同じ標準内ホーンの target pullback を同型で結ぶ。
方針：底上の同じ三つの表示同型を、元の区間 Hom の pullback へ作用させる。
規約：元の二辺と同じ共有頂点を保持する。
使われ方：恒等二単体の target 制限の自明 Kan 性の移送。
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
local notation "H" => cocartesianTwoSimplexStandardHorn k
local notation "T" => cocartesianTwoSimplexLocalTarget k p q

/-- 元の target pullback から同じ標準セルの target pullback への表示比較。 -/
def cocartesianTwoSimplexStandardTargetPullbackMap :
    pullback ((T).map WalkingCospan.Hom.inl) ((T).map WalkingCospan.Hom.inr) ⟶
      pullback (intervalDiagramOverPre P Q (InnerTwoHornOver.toFirst H))
        (intervalDiagramOverPre P Q (InnerTwoHornOver.toSecond H)) :=
  spanPullbackMap _ _ _ _ (cocartesianTwoSimplexStandardTargetSharedMap k p q)
    (cocartesianTwoSimplexStandardTargetFirstMap k p q)
    (cocartesianTwoSimplexStandardTargetSecondMap k p q)
    (cocartesianTwoSimplexStandardTargetFirstMap_naturality k p q)
    (cocartesianTwoSimplexStandardTargetSecondMap_naturality k p q)

/-- 三つの表示比較が同型なので、同じ target pullback の表示比較も同型。 -/
lemma cocartesianTwoSimplexStandardTargetPullbackMap_isIso :
    IsIso (cocartesianTwoSimplexStandardTargetPullbackMap k p q) := by
  have : IsIso (cocartesianTwoSimplexStandardTargetSharedMap k p q) :=
    intervalDiagramOverPre_isIso_of_isIso P Q
      (cocartesianTwoSimplexStandardSharedOverIso k).hom
  have : IsIso (cocartesianTwoSimplexStandardTargetFirstMap k p q) :=
    intervalDiagramOverPre_isIso_of_isIso P Q
      (cocartesianTwoSimplexStandardFirstOverIso k).hom
  have : IsIso (cocartesianTwoSimplexStandardTargetSecondMap k p q) :=
    intervalDiagramOverPre_isIso_of_isIso P Q
      (cocartesianTwoSimplexStandardSecondOverIso k).hom
  exact spanPullbackMap_isIso _ _ _ _ _ _ _ _ _

/-- 同じホーンへの元の制限と、同じ二射影の厳密な pullback 表示の合成。 -/
def cocartesianTwoSimplexStandardHornTargetSegalMap :
    intervalMappingSpace (functorVertex P) (functorVertex Q) ⟶
      pullback (intervalDiagramOverPre P Q (InnerTwoHornOver.toFirst H))
        (intervalDiagramOverPre P Q (InnerTwoHornOver.toSecond H)) :=
  intervalDiagramRestriction H P Q ≫
    (InnerTwoHornOver.intervalDiagram_isPullback P Q H).flip.isoPullback.hom

end SerrePositivity.InfinityCategories
