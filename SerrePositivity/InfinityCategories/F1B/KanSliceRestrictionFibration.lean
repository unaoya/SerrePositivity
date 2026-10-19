module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinSliceRestriction
public import SerrePositivity.InfinityCategories.Core.PullbackRightComposition
public import SerrePositivity.InfinityCategories.Core.SliceRestriction
public import SerrePositivity.InfinityCategories.F1.CosliceRightRestriction

/-!
概要：Kan 拡張の変動する局所形の制限射を、slice の制限の基底変換として扱う。
方針：二つの引き戻しの普遍性を使い、trivial Kan fibration 性を移す。
規約：充填性は直接的な anodyne と持ち上げの API だけを使う。
使われ方：Kerodon Proposition 7.3.6.7 の局所問題の形の変化と、解の組み立て。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：左 Kan の局所形の制限は slice の制限の基底変換。
方針：合成からの pullback の一般比較を使う。
規約：元の図式・制限射は任意。
使われ方：局所形の制限に沿う全境界充填の移送。 -/
lemma kanSliceOverShapeRestrict_isPullback {K L₀ L C : SSet.{u}}
    (δ : K ⟶ C) (p : L ⟶ C) (f : L₀ ⟶ L) :
    IsPullback (pullback.snd δ (sliceOverProjection p)) (kanSliceOverShapeRestrict δ p f)
      (sliceOverRestrict p f) (pullback.snd δ (sliceOverProjection (f ≫ p))) :=
  pullbackMapRightOfComp_isPullback δ (sliceOverProjection (f ≫ p))
    (sliceOverProjection p) (sliceOverRestrict p f) (kanSliceOverRestrict_projection p f).symm

/-- 概要：右 Kan の局所形の制限は coslice の制限の基底変換。
方針：入れ子の引き戻しの lift を構成し、両射影で一意性を証明する。
規約：充填性や単射性を要求しない。
使われ方：右局所形の制限の充填性の比較。 -/
lemma kanSliceUnderShapeRestrict_isPullback {K L₀ L C : SSet.{u}}
    (δ : K ⟶ C) (p : L ⟶ C) (f : L₀ ⟶ L) :
    IsPullback (pullback.fst (sliceUnderProjection p) δ) (kanSliceUnderShapeRestrict δ p f)
      (sliceUnderRestrict p f) (pullback.fst (sliceUnderProjection (f ≫ p)) δ) := by
  refine IsPullback.mk' (kanSliceUnderShapeRestrict_fst δ p f).symm ?_ ?_
  · intro Z φ ψ h₀ h₁
    apply pullback.hom_ext
    · exact h₀
    · have he := congrArg (fun k ↦ k ≫ pullback.snd (sliceUnderProjection (f ≫ p)) δ) h₁
      simpa only [Category.assoc, kanSliceUnderShapeRestrict_snd] using he
  · intro Z a b hab
    have hw : a ≫ sliceUnderProjection p = (b ≫ pullback.snd _ δ) ≫ δ := by
      rw [← sliceUnderRestrict_projection p f, ← Category.assoc, hab,
        Category.assoc, pullback.condition, Category.assoc]
    let H := pullback.lift a (b ≫ pullback.snd _ δ) hw
    refine ⟨H, pullback.lift_fst _ _ _, ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, kanSliceUnderShapeRestrict_fst,
        ← Category.assoc, pullback.lift_fst]
      exact hab
    · rw [Category.assoc, kanSliceUnderShapeRestrict_snd, pullback.lift_snd]

/-- 概要：slice の制限が trivial Kan fibration なら左局所形の制限もそうである。
方針：基底変換で全単射に関する持ち上げ性を保つ。
規約：C の quasicategory 性をこの移送自体には要求しない。
使われ方：形の制限に沿う局所解の持ち上げ。 -/
lemma kanSliceOverShapeRestrict_trivialKanFibration {K L₀ L C : SSet.{u}}
    (δ : K ⟶ C) (p : L ⟶ C) (f : L₀ ⟶ L)
    [TrivialKanFibration (sliceOverRestrict p f)] :
    TrivialKanFibration (kanSliceOverShapeRestrict δ p f) :=
  ⟨trivialKanFibrations.of_isPullback (kanSliceOverShapeRestrict_isPullback δ p f)
    (TrivialKanFibration.mem (p := sliceOverRestrict p f))⟩

/-- 概要：coslice の制限が trivial Kan fibration なら右局所形の制限もそうである。
方針：基底変換による持ち上げ性の保存。
規約：形の制限の充填性を入力とする。
使われ方：右局所解の形の比較。 -/
lemma kanSliceUnderShapeRestrict_trivialKanFibration {K L₀ L C : SSet.{u}}
    (δ : K ⟶ C) (p : L ⟶ C) (f : L₀ ⟶ L)
    [TrivialKanFibration (sliceUnderRestrict p f)] :
    TrivialKanFibration (kanSliceUnderShapeRestrict δ p f) :=
  ⟨trivialKanFibrations.of_isPullback (kanSliceUnderShapeRestrict_isPullback δ p f)
    (TrivialKanFibration.mem (p := sliceUnderRestrict p f))⟩

/-- 概要：left anodyne な固定図式の制限は左局所形の trivial Kan fibration を与える。
方針：slice の制限の充填定理を基底変換する。
規約：C のみ quasicategory とし、K・δ に制限を加えない。
使われ方：局所形を端点や面へ制限する際の持ち上げ。 -/
lemma kanSliceOverShapeRestrict_of_leftAnodyne {K L₀ L C : SSet.{u}} [Quasicategory C]
    (δ : K ⟶ C) (p : L ⟶ C) (f : L₀ ⟶ L) [Mono f]
    (hf : leftAnodyneExtensions f) : TrivialKanFibration (kanSliceOverShapeRestrict δ p f) := by
  have := sliceOverRestrict_trivialKanFibration p f hf
  exact kanSliceOverShapeRestrict_trivialKanFibration δ p f

/-- 概要：right anodyne な部分図式の制限は右局所形の trivial Kan fibration を与える。
方針：coslice の制限の充填定理を基底変換する。
規約：部分複体の包含としての制限を扱う。
使われ方：右局所形を端点や面へ制限する際の持ち上げ。 -/
lemma kanSliceUnderShapeRestrict_of_rightAnodyne {K L C : SSet.{u}} [Quasicategory C]
    (δ : K ⟶ C) (p : L ⟶ C) (A : L.Subcomplex)
    (hA : rightAnodyneExtensions A.ι) :
    TrivialKanFibration (kanSliceUnderShapeRestrict δ p A.ι) := by
  have := sliceUnderRestrict_trivialKanFibration_of_rightAnodyne p A hA
  exact kanSliceUnderShapeRestrict_trivialKanFibration δ p A.ι

end SerrePositivity.InfinityCategories
