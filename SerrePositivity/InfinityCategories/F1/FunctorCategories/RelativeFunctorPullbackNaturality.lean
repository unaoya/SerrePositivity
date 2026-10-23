module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPullback
public import SerrePositivity.InfinityCategories.F1.Fibrations.FiberComparisonBaseChange
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPostUncurry
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorSquarePost

/-!
概要：相対 Hom の実際の引き戻しは、底上の通常の前後合成と厳密に可換。
方針：引き戻しの第一射影の式と相対 uncurry を使い、二射影で全ての族を比較する。
規約：充填性や同値性は不要。元の relativeFunctorPullback の全パラメーターの作用。
使われ方：一般の left fibration 対を、復元射で元の coherent unstraightening 対へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 比較射の底変換は、元の全空間への第一射影の後に元の比較を回収する。 -/
lemma fiberComparisonBaseChange_fst {E F B D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p) (k : D ⟶ B) :
    fiberComparisonBaseChange p q f hf k ≫ pullback.fst q k = pullback.fst p k ≫ f :=
  pullback.lift_fst _ _ _

/-- 相対 Hom の引き戻しは、標的の底上の射による後合成と厳密に可換。 -/
lemma relativeFunctorPullback_post {A E F B D : SSet.{u}}
    (a : A ⟶ B) (p : E ⟶ B) (q : F ⟶ B)
    (f : E ⟶ F) (hf : f ≫ q = p) (k : D ⟶ B) :
    HomotopyLimits.relativeFunctorPost p q f hf a ≫ relativeFunctorPullback a q k =
    relativeFunctorPullback a p k ≫
      HomotopyLimits.relativeFunctorPost (pullback.snd p k) (pullback.snd q k)
        (fiberComparisonBaseChange p q f hf k)
        (fiberComparisonBaseChange_projection p q f hf k) (pullback.snd a k) := by
  apply relativeFunctorUncurry_injective
  apply pullback.hom_ext
  · rw [relativeFunctorPullback_uncurry_fst, relativeFunctorPost_uncurry]
    simp only [Category.assoc]
    rw [fiberComparisonBaseChange_fst]
    have hp := relativeFunctorPost_uncurry p q f hf a (𝟙 _)
    have hk := relativeFunctorPullback_uncurry_fst a p k (𝟙 _)
    simp only [Category.id_comp] at hp hk
    rw [hp, ← Category.assoc _ (pullback.fst p k) f, hk, Category.assoc]
  · rw [relativeFunctorUncurry_projection, relativeFunctorUncurry_projection]

/-- 相対 Hom の引き戻しは、始域の底上の射による前合成と厳密に可換。 -/
lemma relativeFunctorPullback_pre {E B D : SSet.{u}}
    (p : E ⟶ B) {a b : Over B} (f : a ⟶ b) (k : D ⟶ B) :
    relativeFunctorOverPre p f ≫ relativeFunctorPullback a.hom p k =
    relativeFunctorPullback b.hom p k ≫ relativeFunctorOverPre (pullback.snd p k)
      (Over.homMk (U := Over.mk (pullback.snd a.hom k))
        (V := Over.mk (pullback.snd b.hom k))
        (fiberComparisonBaseChange a.hom b.hom f.left f.w k)
        (fiberComparisonBaseChange_projection a.hom b.hom f.left f.w k)) := by
  apply relativeFunctorUncurry_injective
  apply pullback.hom_ext
  · rw [relativeFunctorPullback_uncurry_fst]
    have hpre := relativeFunctorOverPre_uncurry (pullback.snd p k)
      (Over.homMk (U := Over.mk (pullback.snd a.hom k))
        (V := Over.mk (pullback.snd b.hom k))
        (fiberComparisonBaseChange a.hom b.hom f.left f.w k)
        (fiberComparisonBaseChange_projection a.hom b.hom f.left f.w k))
      (relativeFunctorPullback b.hom p k)
    refine Eq.trans ?_ (congrArg (fun t ↦ t ≫ pullback.fst p k) hpre).symm
    simp only [Category.assoc]
    have hp := relativeFunctorOverPre_uncurry p f (𝟙 _)
    have hk := relativeFunctorPullback_uncurry_fst b.hom p k (𝟙 _)
    simp only [Category.id_comp] at hp hk
    rw [hp, hk]
    simp only [← Category.assoc, ← comp_whiskerRight, Over.homMk_left]
    rw [fiberComparisonBaseChange_fst]
  · rw [relativeFunctorUncurry_projection, relativeFunctorUncurry_projection]

end SerrePositivity.InfinityCategories
