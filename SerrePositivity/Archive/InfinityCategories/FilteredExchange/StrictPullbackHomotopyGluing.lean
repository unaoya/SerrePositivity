module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.HomotopyRepresentativeLift
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
概要：共通の底で同じ類を持つ二脚のホモトピーを、厳密な引き戻し全体へ貼り合わせる。
方針：左の代表を右の底の全円柱と厳密に揃えてから、引き戻しへ入れる。
規約：両端と右の全円柱を保持。使われ方：native 切断と実模型の比較の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {T L M R : SSet.{u}} (p : L ⟶ M) (q : R ⟶ M)
  (a b : T ⟶ pullback p q)

/-- 右脚の全ホモトピーを、厳密な引き戻しの左脚の底へ端点だけ表示変更する。 -/
def strictPullbackRightHomotopyBase
    (H : SSet.Homotopy (a ≫ pullback.snd p q) (b ≫ pullback.snd p q)) :
    SSet.Homotopy ((a ≫ pullback.fst p q) ≫ p) ((b ≫ pullback.fst p q) ≫ p) where
  h := H.h ≫ q
  h₀ := by
    change _ = (a ≫ pullback.fst p q) ≫ p
    rw [← Category.assoc, H.h₀]
    simp only [Category.assoc, pullback.condition]
  h₁ := by
    change _ = (b ≫ pullback.fst p q) ≫ p
    rw [← Category.assoc, H.h₁]
    simp only [Category.assoc, pullback.condition]
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 底の二つの指定類が一致すれば、右の全円柱を保つ全体のホモトピーが存在する。 -/
lemma strictPullback_exists_homotopy [Quasicategory L] [Quasicategory M] [InnerFibration p]
    (H : SSet.Homotopy (a ≫ pullback.fst p q) (b ≫ pullback.fst p q))
    (K : SSet.Homotopy (a ≫ pullback.snd p q) (b ≫ pullback.snd p q))
    (h : SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp H p)) =
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (strictPullbackRightHomotopyBase p q a b K))) :
    ∃ V : SSet.Homotopy a b, V.h ≫ pullback.snd p q = K.h ∧
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp V (pullback.fst p q))) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) := by
  obtain ⟨H', hp, hc⟩ := F1B.exists_kanHomotopyRepresentative_lift p H
    (strictPullbackRightHomotopyBase p q a b K) h
  let V : SSet.Homotopy a b :=
    { h := pullback.lift H'.h K.h hp
      h₀ := by
        change _ = a
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst]
          exact H'.h₀
        · rw [Category.assoc, pullback.lift_snd]
          exact K.h₀
      h₁ := by
        change _ = b
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst]
          exact H'.h₁
        · rw [Category.assoc, pullback.lift_snd]
          exact K.h₁
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro x
        exact False.elim x.1.property }
  refine ⟨V, pullback.lift_snd _ _ _, ?_⟩
  have hV : functorHomotopyPostcomp V (pullback.fst p q) = H' := by
    apply SSet.RelativeMorphism.Homotopy.ext
    exact pullback.lift_fst _ _ _
  rw [hV]
  exact hc

end SerrePositivity.InfinityCategories.F2
