module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：共通部分を拡大する二つの pushout の比較自体を pushout として表示する。
方針：上側の pushout を消去した後、左側の pushout を消去する。
規約：任意の圏の実際の射について述べ、単射性を要求しない。
使われ方：有限セルの余極限構成で、相対 join 境界の付着を移す。
-/

@[expose] public section
noncomputable section
universe v u
open CategoryTheory Limits
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
variable {C : Type u} [Category.{v} C] [HasPushouts C]
variable {O A B D Z : C} (a : O ⟶ A) (s : O ⟶ D) (f : A ⟶ B)

/-- 共通部分 O からの付着において A を B へ拡大する実比較。 -/
def pushoutCornerExpansion : pushout s a ⟶ pushout s (a ≫ f) :=
  pushout.desc (pushout.inl _ _) (f ≫ pushout.inr _ _) (by
    rw [← Category.assoc, pushout.condition])

/-- 共通部分の拡大は、元の射 f の pushout。 -/
lemma pushoutCornerExpansion_isPushout :
    IsPushout (pushout.inr s a) f (pushoutCornerExpansion a s f)
      (pushout.inr s (a ≫ f)) := by
  have ho : IsPushout s (a ≫ f)
      (pushout.inl s a ≫ pushoutCornerExpansion a s f) (pushout.inr s (a ≫ f)) := by
    simpa only [pushoutCornerExpansion, pushout.inl_desc] using
      (IsPushout.of_hasPushout s (a ≫ f))
  exact ho.of_top
    (show pushout.inr s a ≫ pushoutCornerExpansion a s f =
      f ≫ pushout.inr s (a ≫ f) from pushout.inr_desc _ _ _)
    (IsPushout.of_hasPushout s a)

variable (j : A ⟶ Z) (d : D ⟶ Z) (h : s ≫ d = a ≫ j)

/-- 付着前の二つの射を貼る比較。 -/
def pushoutCornerBoundary : pushout s a ⟶ Z := pushout.desc d j h

/-- 付着後の二つの射を貼る比較。 -/
def pushoutCornerTarget : pushout s (a ≫ f) ⟶ pushout f j :=
  pushout.desc (d ≫ pushout.inr f j) (pushout.inl f j) (by
    rw [← Category.assoc, h, Category.assoc, Category.assoc]
    exact congrArg (a ≫ ·) (pushout.condition (f := f) (g := j)).symm)

/-- 相対境界からの拡大は、境界比較の pushout である。 -/
lemma pushoutCornerComparison_isPushout :
    IsPushout (pushoutCornerBoundary a s j d h) (pushoutCornerExpansion a s f)
      (pushout.inr f j) (pushoutCornerTarget a s f j d h) := by
  have hc : pushoutCornerBoundary a s j d h ≫ pushout.inr f j =
      pushoutCornerExpansion a s f ≫ pushoutCornerTarget a s f j d h := by
    apply pushout.hom_ext
    · simp [pushoutCornerBoundary, pushoutCornerExpansion, pushoutCornerTarget,
        Category.assoc]
    · simp only [pushoutCornerBoundary, pushoutCornerExpansion, pushoutCornerTarget,
        pushout.inr_desc_assoc, Category.assoc, pushout.inr_desc]
      exact (pushout.condition (f := f) (g := j)).symm
  have ho : IsPushout
      (pushout.inr s a ≫ pushoutCornerBoundary a s j d h) f (pushout.inr f j)
      (pushout.inr s (a ≫ f) ≫ pushoutCornerTarget a s f j d h) := by
    simpa only [pushoutCornerBoundary, pushoutCornerTarget, pushout.inr_desc] using
      (IsPushout.of_hasPushout f j).flip
  exact ho.of_left hc (pushoutCornerExpansion_isPushout a s f)

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
