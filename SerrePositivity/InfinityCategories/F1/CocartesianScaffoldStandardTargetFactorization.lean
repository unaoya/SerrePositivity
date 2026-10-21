module

public import SerrePositivity.InfinityCategories.F1.CocartesianScaffoldStandardTargetPullback
public import SerrePositivity.InfinityCategories.F1.CocartesianScaffoldTargetFactorization

/-!
概要：元の target 制限は、表示同型の後で同じ同じ貼合せの制限と一致する。
方針：同じ二射影を展開し、底上の制限の厳密な自然性を使う。
規約：元の最初の辺と尾部・共有頂点・分類図式を保持する。
使われ方：同じ貼合せへの自明 Kan 制限を元の target 制限へ移す。
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

/-- 表示比較の最初の射影は、同じ最初の標準セルへの制限。 -/
lemma cocartesianScaffoldStandardTargetPullbackMap_fst :
    cocartesianScaffoldStandardTargetPullbackMap n k p q ≫ pullback.fst _ _ =
    pullback.fst ((T).map WalkingCospan.Hom.inl) ((T).map WalkingCospan.Hom.inr) ≫
      cocartesianScaffoldStandardTargetFirstMap n k p q :=
  spanPullbackMap_fst _ _ _ _ _ _ _ _ _

/-- 表示比較の次の射影は、同じ次の標準セルへの制限。 -/
lemma cocartesianScaffoldStandardTargetPullbackMap_snd :
    cocartesianScaffoldStandardTargetPullbackMap n k p q ≫ pullback.snd _ _ =
    pullback.snd ((T).map WalkingCospan.Hom.inl) ((T).map WalkingCospan.Hom.inr) ≫
      cocartesianScaffoldStandardTargetSecondMap n k p q :=
  spanPullbackMap_snd _ _ _ _ _ _ _ _ _

/-- 元の target 制限は、同じ表示同型の後で同じ貼合せの Segal 射そのものになる。 -/
lemma cocartesianScaffoldTargetRestrictionMap_standard_factor :
    cocartesianScaffoldTargetRestrictionMap n k p q ≫
      cocartesianScaffoldStandardTargetPullbackMap n k p q =
    cocartesianScaffoldTargetSegalMap n k p q := by
  apply pullback.hom_ext
  · rw [Category.assoc, cocartesianScaffoldStandardTargetPullbackMap_fst,
      ← Category.assoc, cocartesianScaffoldTargetRestrictionMap_fst,
      cocartesianScaffoldTargetSegalMap_fst]
    exact intervalDiagramOverPre_restriction P Q
      (cocartesianScaffoldLargeFirstOverIso n k).hom
  · rw [Category.assoc, cocartesianScaffoldStandardTargetPullbackMap_snd,
      ← Category.assoc, cocartesianScaffoldTargetRestrictionMap_snd,
      cocartesianScaffoldTargetSegalMap_snd]
    exact intervalDiagramOverPre_restriction P Q
      (cocartesianScaffoldLargeTailOverIso n k).hom

end SerrePositivity.InfinityCategories
