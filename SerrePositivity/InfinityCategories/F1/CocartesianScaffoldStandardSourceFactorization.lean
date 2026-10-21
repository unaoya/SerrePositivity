module

public import SerrePositivity.InfinityCategories.F1.CocartesianScaffoldStandardSourcePullback
public import SerrePositivity.InfinityCategories.F1.CocartesianScaffoldSourceRestrictionMap

/-!
概要：元の source 制限は表示同型の後で同じ同じ貼合せの native core 制限に一致する。
方針：同じ二射影で元の底上の制限の自然性を照合する。
規約：元の全相対 Hom と同じ native core 制限を保持する。
使われ方：同じ貼合せ像への自明 Kan 制限を元の source 制限へ移す。
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
local notation "S" => cocartesianScaffoldLocalSource n k p q

/-- source 表示比較の最初の射影は同じ標準区間への native core 制限。 -/
lemma cocartesianScaffoldStandardSourcePullbackMap_fst :
    cocartesianScaffoldStandardSourcePullbackMap n k p q ≫ pullback.fst _ _ =
    pullback.fst ((S).map WalkingCospan.Hom.inl) ((S).map WalkingCospan.Hom.inr) ≫
      cocartesianScaffoldStandardSourceFirstMap n k p q :=
  spanPullbackMap_fst _ _ _ _ _ _ _ _ _

/-- source 表示比較の次の射影も同じ標準区間への native core 制限。 -/
lemma cocartesianScaffoldStandardSourcePullbackMap_snd :
    cocartesianScaffoldStandardSourcePullbackMap n k p q ≫ pullback.snd _ _ =
    pullback.snd ((S).map WalkingCospan.Hom.inl) ((S).map WalkingCospan.Hom.inr) ≫
      cocartesianScaffoldStandardSourceSecondMap n k p q :=
  spanPullbackMap_snd _ _ _ _ _ _ _ _ _

/-- 同じ source Segal 射の最初の射影は、同じ標準区間への直接制限。 -/
lemma cocartesianScaffoldStandardBridgeSourceSegalMap_fst :
    cocartesianScaffoldStandardBridgeSourceSegalMap n k p q ≫ pullback.fst _ _ =
      cocartesianPullbackNativeLiftRestriction P Q (ScaffoldBridgeOver.first n H) := by
  rw [cocartesianScaffoldStandardBridgeSourceSegalMap, Category.assoc,
    IsPullback.isoPullback_hom_fst]
  exact cocartesianPullbackNativeLiftRestriction_naturality P Q
    (ScaffoldBridgeOver.firstInclusion n H)

/-- 同じ source Segal 射の次の射影も、同じ標準区間への直接制限。 -/
lemma cocartesianScaffoldStandardBridgeSourceSegalMap_snd :
    cocartesianScaffoldStandardBridgeSourceSegalMap n k p q ≫ pullback.snd _ _ =
      cocartesianPullbackNativeLiftRestriction P Q (ScaffoldBridgeOver.tail n H) := by
  rw [cocartesianScaffoldStandardBridgeSourceSegalMap, Category.assoc,
    IsPullback.isoPullback_hom_snd]
  exact cocartesianPullbackNativeLiftRestriction_naturality P Q
    (ScaffoldBridgeOver.tailInclusion n H)

/-- 元の source 制限は、同じ表示同型の後で同じ貼合せの native core 制限そのもの。 -/
lemma cocartesianScaffoldSourceRestrictionMap_standard_factor :
    cocartesianScaffoldSourceRestrictionMap n k p q ≫
      cocartesianScaffoldStandardSourcePullbackMap n k p q =
    cocartesianScaffoldStandardBridgeSourceSegalMap n k p q := by
  apply pullback.hom_ext
  · rw [Category.assoc, cocartesianScaffoldStandardSourcePullbackMap_fst,
      ← Category.assoc, cocartesianScaffoldSourceRestrictionMap_fst,
      cocartesianScaffoldStandardBridgeSourceSegalMap_fst]
    exact cocartesianPullbackNativeLiftRestriction_naturality P Q
      (cocartesianScaffoldSmallFirstOverIso n k).hom
  · rw [Category.assoc, cocartesianScaffoldStandardSourcePullbackMap_snd,
      ← Category.assoc, cocartesianScaffoldSourceRestrictionMap_snd,
      cocartesianScaffoldStandardBridgeSourceSegalMap_snd]
    exact cocartesianPullbackNativeLiftRestriction_naturality P Q
      (cocartesianScaffoldSmallTailOverIso n k).hom

end SerrePositivity.InfinityCategories
