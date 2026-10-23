module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexStandardTargetPullback
public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexTargetFactorization

/-!
概要：元の target 制限は、表示同型の後で同じ標準内ホーンの制限と一致する。
方針：同じ二射影を展開し、底上の制限の厳密な自然性を使う。
規約：元の二辺・共有頂点・分類図式を保持する。
使われ方：標準ホーンへの自明 Kan 制限を元の target 制限へ移す。
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

/-- 表示比較の最初の射影は、同じ最初の標準セルへの制限。 -/
lemma cocartesianTwoSimplexStandardTargetPullbackMap_fst :
    cocartesianTwoSimplexStandardTargetPullbackMap k p q ≫ pullback.fst _ _ =
    pullback.fst ((T).map WalkingCospan.Hom.inl) ((T).map WalkingCospan.Hom.inr) ≫
      cocartesianTwoSimplexStandardTargetFirstMap k p q :=
  spanPullbackMap_fst _ _ _ _ _ _ _ _ _

/-- 表示比較の次の射影は、同じ次の標準セルへの制限。 -/
lemma cocartesianTwoSimplexStandardTargetPullbackMap_snd :
    cocartesianTwoSimplexStandardTargetPullbackMap k p q ≫ pullback.snd _ _ =
    pullback.snd ((T).map WalkingCospan.Hom.inl) ((T).map WalkingCospan.Hom.inr) ≫
      cocartesianTwoSimplexStandardTargetSecondMap k p q :=
  spanPullbackMap_snd _ _ _ _ _ _ _ _ _

/-- 標準ホーンの Segal 射の最初の射影は同じ標準区間への直接制限。 -/
lemma cocartesianTwoSimplexStandardHornTargetSegalMap_fst :
    cocartesianTwoSimplexStandardHornTargetSegalMap k p q ≫ pullback.fst _ _ =
      intervalDiagramRestriction (InnerTwoHornOver.first H).hom P Q := by
  rw [cocartesianTwoSimplexStandardHornTargetSegalMap, Category.assoc,
    IsPullback.isoPullback_hom_fst]
  exact intervalDiagramOverPre_restriction P Q (InnerTwoHornOver.firstInclusion H)

/-- 標準ホーンの Segal 射の次の射影も同じ標準区間への直接制限。 -/
lemma cocartesianTwoSimplexStandardHornTargetSegalMap_snd :
    cocartesianTwoSimplexStandardHornTargetSegalMap k p q ≫ pullback.snd _ _ =
      intervalDiagramRestriction (InnerTwoHornOver.second H).hom P Q := by
  rw [cocartesianTwoSimplexStandardHornTargetSegalMap, Category.assoc,
    IsPullback.isoPullback_hom_snd]
  exact intervalDiagramOverPre_restriction P Q (InnerTwoHornOver.secondInclusion H)

/-- 元の target 制限は、同じ表示同型の後で標準ホーンの Segal 射そのものになる。 -/
lemma cocartesianTwoSimplexTargetRestrictionMap_standard_factor :
    cocartesianTwoSimplexTargetRestrictionMap k p q ≫
      cocartesianTwoSimplexStandardTargetPullbackMap k p q =
    cocartesianTwoSimplexStandardHornTargetSegalMap k p q := by
  apply pullback.hom_ext
  · rw [Category.assoc, cocartesianTwoSimplexStandardTargetPullbackMap_fst,
      ← Category.assoc, cocartesianTwoSimplexTargetRestrictionMap_fst,
      cocartesianTwoSimplexStandardHornTargetSegalMap_fst]
    exact intervalDiagramOverPre_restriction P Q
      (cocartesianTwoSimplexStandardFirstOverIso k).hom
  · rw [Category.assoc, cocartesianTwoSimplexStandardTargetPullbackMap_snd,
      ← Category.assoc, cocartesianTwoSimplexTargetRestrictionMap_snd,
      cocartesianTwoSimplexStandardHornTargetSegalMap_snd]
    exact intervalDiagramOverPre_restriction P Q
      (cocartesianTwoSimplexStandardSecondOverIso k).hom

end SerrePositivity.InfinityCategories
