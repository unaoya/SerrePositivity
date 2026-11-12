module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeFamilyPullbackComponents
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：錐族と厳密な引き戻しの交換。
方針：二成分を保つ全パラメータの lift と一意性を極限錐へまとめる。
規約：元の図式の錐族そのものを頂点に取る。
使われ方：成分ごとの極限錐判定と lax pullback の安定性。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {J E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B) (r : J ⟶ pullback p q)

/-- 概要：元の錐族を頂点とする成分錐族の引き戻し錐。
方針：元の二射影による後合成を脚とする。
規約：共通の底の図式は第一成分の像。
使われ方：錐族の交換同型と元の脚の同定。 -/
def coneFamilyPullbackCone : PullbackCone
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyPostcomp (r ≫ pullback.fst p q) p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyPullbackBaseMap p q r) :=
  PullbackCone.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyPostcomp r (pullback.fst p q))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyPostcomp r (pullback.snd p q)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyPullback_condition p q r)

/-- 概要：元の錐族を頂点とする錐は厳密な極限錐。
方針：指定二成分の lift とその一意性を使う。
規約：quasicategory 性や元の関手の充填性は不要。
使われ方：錐族の引き戻しの普遍性。 -/
def coneFamilyPullbackCone_isLimit : IsLimit (coneFamilyPullbackCone p q r) :=
  PullbackCone.IsLimit.mk _ (fun s ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyPullbackLift p q r s.fst s.snd s.condition)
    (fun _ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyPullbackLift_fst ..) (fun _ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyPullbackLift_snd ..)
    (fun s _m hm₁ hm₂ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyPullback_hom_ext p q r
      (hm₁.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyPullbackLift_fst p q r s.fst s.snd s.condition).symm)
      (hm₂.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyPullbackLift_snd p q r s.fst s.snd s.condition).symm))

/-- 概要：錐族の二射影の正方形は厳密な引き戻し。
方針：元の錐族の極限錐を使う。
規約：全次数で図式を固定する錐の族を比較する。
使われ方：元の錐の成分ごとの極限性。 -/
lemma coneFamilyPullback_isPullback :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyPostcomp r (pullback.fst p q))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyPostcomp r (pullback.snd p q))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyPostcomp (r ≫ pullback.fst p q) p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyPullbackBaseMap p q r) :=
  IsPullback.of_isLimit (coneFamilyPullbackCone_isLimit p q r)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
