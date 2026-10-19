module

public import SerrePositivity.InfinityCategories.F2.LaxPullbackColimitCriterion
public import SerrePositivity.InfinityCategories.Stable.Definition

/-!
概要：有限余極限を保つ二関手の lax pullback の有限余極限と成分判定。
方針：各有限図式に両入力の余極限の存在と成分ごとの判定を適用する。
規約：保存性は元の関手 p・q にだけ仮定する。
使われ方：安定性の構成と射影の有限余極限保存。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
variable [HasFiniteColimits A] [HasFiniteColimits B] (p : A ⟶ C) (q : B ⟶ C)
variable (hp : ∀ {J : SSet.{u}} [J.Finite] {r : J ⟶ A} (c : JoinCocone r),
  IsColimitCone c → IsColimitCone (F1B.kanPostcomposeCocone p c))
variable (hq : ∀ {J : SSet.{u}} [J.Finite] {r : J ⟶ B} (c : JoinCocone r),
  IsColimitCone c → IsColimitCone (F1B.kanPostcomposeCocone q c))
include hp hq

/-- 概要：有限余極限を保つ二関手の lax pullback は全ての有限余極限を持つ。
方針：各有限図式の入力の余極限を元の二関手で保ち、全体の余極限を構成する。
規約：C の全有限余極限の存在は要求しない。
使われ方：Tamme Lemma 8(iv) の有限余極限の存在。 -/
lemma hasFiniteColimits_laxPullback_of_preservation : HasFiniteColimits (laxPullback p q) where
  hasColimit r := hasColimit_laxPullback_of_components p q r
    (HasFiniteColimits.hasColimit _) (HasFiniteColimits.hasColimit _)
    (fun c hc ↦ hp c hc) (fun c hc ↦ hq c hc)

/-- 概要：有限錐の余極限性は元の二射影の錐の余極限性と同値。
方針：有限な入力図式の余極限の存在と元の関手の保存を成分判定へ渡す。
規約：元の指定余錐を変更しない。
使われ方：射影の有限余極限保存と成分ごとの計算。 -/
lemma isColimitCone_laxPullback_iff_finite_components {J : SSet.{u}} [J.Finite]
    {r : J ⟶ laxPullback p q} (c : JoinCocone r) :
    IsColimitCone c ↔ IsColimitCone (F1B.kanPostcomposeCocone (laxPullbackFst p q) c) ∧
      IsColimitCone (F1B.kanPostcomposeCocone (laxPullbackSnd p q) c) :=
  isColimitCone_laxPullback_iff_components p q r
    (HasFiniteColimits.hasColimit _) (HasFiniteColimits.hasColimit _)
    (fun d hd ↦ hp d hd) (fun d hd ↦ hq d hd) c

end SerrePositivity.InfinityCategories.F2
