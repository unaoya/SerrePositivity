module

public import SerrePositivity.InfinityCategories.Core.SliceRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.SliceEndpointConeComparison

/-!
概要：元の対象を始点とする全錐の comma の形状制限。
方針：slice の制限を同じ射の上で引き戻し、その実際の比較正方形を証明する。
規約：全射と始点射影を保持。使われ方：有限半順序図式の上方区間から始対象への比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits
variable {A K J X : SSet.{u}} (δ : A ⟶ X) (D : K ⟶ X) (i : J ⟶ K)

/-- 同じ始点を保って元の全錐を部分形状へ制限する実際の comma 射。 -/
def coneCommaRestriction : pullback δ (sliceOverProjection D) ⟶
    pullback δ (sliceOverProjection (i ≫ D)) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ sliceOverRestrict D i) (by
    rw [Category.assoc, sliceOverRestrict_projection]
    exact pullback.condition)

/-- 始点図式への射影は厳密に変わらない。 -/
lemma coneCommaRestriction_fst : coneCommaRestriction δ D i ≫ pullback.fst _ _ =
    pullback.fst δ (sliceOverProjection D) := pullback.lift_fst _ _ _

/-- 全錐への第二射影は元の slice 制限そのもの。 -/
lemma coneCommaRestriction_snd : coneCommaRestriction δ D i ≫ pullback.snd _ _ =
    pullback.snd δ (sliceOverProjection D) ≫ sliceOverRestrict D i :=
  pullback.lift_snd _ _ _

/-- 元の comma 制限は元の slice 制限の厳密な引き戻し。 -/
lemma coneCommaRestriction_isPullback :
    IsPullback (pullback.snd δ (sliceOverProjection D)) (coneCommaRestriction δ D i)
      (sliceOverRestrict D i) (pullback.snd δ (sliceOverProjection (i ≫ D))) := by
  refine IsPullback.mk' (coneCommaRestriction_snd δ D i).symm ?_ ?_
  · intro T a b ha hb
    apply pullback.hom_ext
    · have h := congrArg (fun f => f ≫ pullback.fst δ (sliceOverProjection (i ≫ D))) hb
      simpa only [Category.assoc, coneCommaRestriction_fst] using h
    · exact ha
  · intro T a b hab
    let L := pullback.lift (f := δ) (g := sliceOverProjection D)
      (b ≫ pullback.fst δ (sliceOverProjection (i ≫ D))) a (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, ← hab, Category.assoc,
        sliceOverRestrict_projection])
    refine ⟨L, pullback.lift_snd _ _ _, ?_⟩
    apply pullback.hom_ext
    · simp only [Category.assoc, coneCommaRestriction_fst, L, pullback.lift_fst]
    · simpa only [Category.assoc, coneCommaRestriction_snd, L,
        pullback.lift_snd_assoc] using hab

/-- left anodyne な制限は、元の全 comma の間で自明 Kan fibration。 -/
lemma coneCommaRestriction_trivialKanFibration [Quasicategory X] [Mono i]
    (hi : leftAnodyneExtensions i) : TrivialKanFibration (coneCommaRestriction δ D i) := by
  have := sliceOverRestrict_trivialKanFibration D i hi
  exact ⟨trivialKanFibrations.of_isPullback (coneCommaRestriction_isPullback δ D i)
    TrivialKanFibration.mem⟩

end SerrePositivity.InfinityCategories.F2.Ind
