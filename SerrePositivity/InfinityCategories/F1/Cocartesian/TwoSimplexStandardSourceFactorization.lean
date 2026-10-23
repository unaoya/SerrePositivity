module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexStandardSourcePullback
public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexSourceRestrictionMap

/-!
概要：元の source 制限は表示同型の後で同じ標準内ホーンの native core 制限に一致する。
方針：同じ二射影で元の底上の制限の自然性を照合する。
規約：元の全相対 Hom と同じ native core 制限を保持する。
使われ方：標準内ホーン像への自明 Kan 制限を元の source 制限へ移す。
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
local notation "S" => cocartesianTwoSimplexLocalSource k p q

/-- source 表示比較の最初の射影は同じ標準区間への native core 制限。 -/
lemma cocartesianTwoSimplexStandardSourcePullbackMap_fst :
    cocartesianTwoSimplexStandardSourcePullbackMap k p q ≫ pullback.fst _ _ =
    pullback.fst ((S).map WalkingCospan.Hom.inl) ((S).map WalkingCospan.Hom.inr) ≫
      cocartesianTwoSimplexStandardSourceFirstMap k p q :=
  spanPullbackMap_fst _ _ _ _ _ _ _ _ _

/-- source 表示比較の次の射影も同じ標準区間への native core 制限。 -/
lemma cocartesianTwoSimplexStandardSourcePullbackMap_snd :
    cocartesianTwoSimplexStandardSourcePullbackMap k p q ≫ pullback.snd _ _ =
    pullback.snd ((S).map WalkingCospan.Hom.inl) ((S).map WalkingCospan.Hom.inr) ≫
      cocartesianTwoSimplexStandardSourceSecondMap k p q :=
  spanPullbackMap_snd _ _ _ _ _ _ _ _ _

/-- 同じ source Segal 射の最初の射影は、同じ標準区間への直接制限。 -/
lemma cocartesianTwoSimplexStandardHornSourceSegalMap_fst :
    cocartesianTwoSimplexStandardHornSourceSegalMap k p q ≫ pullback.fst _ _ =
      cocartesianPullbackNativeLiftRestriction P Q (InnerTwoHornOver.first H) := by
  rw [cocartesianTwoSimplexStandardHornSourceSegalMap, Category.assoc,
    IsPullback.isoPullback_hom_fst]
  exact cocartesianPullbackNativeLiftRestriction_naturality P Q
    (InnerTwoHornOver.firstInclusion H)

/-- 同じ source Segal 射の次の射影も、同じ標準区間への直接制限。 -/
lemma cocartesianTwoSimplexStandardHornSourceSegalMap_snd :
    cocartesianTwoSimplexStandardHornSourceSegalMap k p q ≫ pullback.snd _ _ =
      cocartesianPullbackNativeLiftRestriction P Q (InnerTwoHornOver.second H) := by
  rw [cocartesianTwoSimplexStandardHornSourceSegalMap, Category.assoc,
    IsPullback.isoPullback_hom_snd]
  exact cocartesianPullbackNativeLiftRestriction_naturality P Q
    (InnerTwoHornOver.secondInclusion H)

/-- 元の source 制限は、同じ表示同型の後で標準内ホーンの native core 制限そのもの。 -/
lemma cocartesianTwoSimplexSourceRestrictionMap_standard_factor :
    cocartesianTwoSimplexSourceRestrictionMap k p q ≫
      cocartesianTwoSimplexStandardSourcePullbackMap k p q =
    cocartesianTwoSimplexStandardHornSourceSegalMap k p q := by
  apply pullback.hom_ext
  · rw [Category.assoc, cocartesianTwoSimplexStandardSourcePullbackMap_fst,
      ← Category.assoc, cocartesianTwoSimplexSourceRestrictionMap_fst,
      cocartesianTwoSimplexStandardHornSourceSegalMap_fst]
    exact cocartesianPullbackNativeLiftRestriction_naturality P Q
      (cocartesianTwoSimplexSmallStandardFirstOverIso k).hom
  · rw [Category.assoc, cocartesianTwoSimplexStandardSourcePullbackMap_snd,
      ← Category.assoc, cocartesianTwoSimplexSourceRestrictionMap_snd,
      cocartesianTwoSimplexStandardHornSourceSegalMap_snd]
    exact cocartesianPullbackNativeLiftRestriction_naturality P Q
      (cocartesianTwoSimplexSmallStandardSecondOverIso k).hom

end SerrePositivity.InfinityCategories
