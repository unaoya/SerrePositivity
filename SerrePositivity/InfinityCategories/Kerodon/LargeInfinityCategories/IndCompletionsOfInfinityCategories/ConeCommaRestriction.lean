module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SliceEndpointConeComparison

/-!
概要：元の対象を始点とする全錐の comma の形状制限。
方針：slice の制限を同じ射の上で引き戻し、その実際の比較正方形を証明する。
規約：全射と始点射影を保持。使われ方：有限半順序図式の上方区間から始対象への比較。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

variable {A K J X : SSet.{u}} (δ : A ⟶ X) (D : K ⟶ X) (i : J ⟶ K)

/-- 同じ始点を保って元の全錐を部分形状へ制限する実際の comma 射。 -/
def coneCommaRestriction : pullback δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection D) ⟶
    pullback δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (i ≫ D)) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict D i) (by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sliceOverRestrict_projection]
    exact pullback.condition)

/-- 始点図式への射影は厳密に変わらない。 -/
lemma coneCommaRestriction_fst : coneCommaRestriction δ D i ≫ pullback.fst _ _ =
    pullback.fst δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection D) := pullback.lift_fst _ _ _

/-- 全錐への第二射影は元の slice 制限そのもの。 -/
lemma coneCommaRestriction_snd : coneCommaRestriction δ D i ≫ pullback.snd _ _ =
    pullback.snd δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection D) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict D i :=
  pullback.lift_snd _ _ _

/-- 元の comma 制限は元の slice 制限の厳密な引き戻し。 -/
lemma coneCommaRestriction_isPullback :
    IsPullback (pullback.snd δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection D)) (coneCommaRestriction δ D i)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict D i) (pullback.snd δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (i ≫ D))) := by
  refine IsPullback.mk' (coneCommaRestriction_snd δ D i).symm ?_ ?_
  · intro T a b ha hb
    apply pullback.hom_ext
    · have h := congrArg (fun f => f ≫ pullback.fst δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (i ≫ D))) hb
      simpa only [Category.assoc, coneCommaRestriction_fst] using h
    · exact ha
  · intro T a b hab
    let L := pullback.lift (f := δ) (g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection D)
      (b ≫ pullback.fst δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (i ≫ D))) a (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, ← hab, Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sliceOverRestrict_projection])
    refine ⟨L, pullback.lift_snd _ _ _, ?_⟩
    apply pullback.hom_ext
    · simp only [Category.assoc, coneCommaRestriction_fst, L, pullback.lift_fst]
    · simpa only [Category.assoc, coneCommaRestriction_snd, L,
        pullback.lift_snd_assoc] using hab

/-- left anodyne な制限は、元の全 comma の間で自明 Kan fibration。 -/
lemma coneCommaRestriction_trivialKanFibration [Quasicategory X] [Mono i]
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (coneCommaRestriction δ D i) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict_trivialKanFibration D i hi
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.of_isPullback (coneCommaRestriction_isPullback δ D i)
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
