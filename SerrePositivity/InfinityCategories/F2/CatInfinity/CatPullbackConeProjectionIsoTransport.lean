module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackConeProjections

/-!
概要：二射影の指定比較同型の端点輸送の前の値。
方針：構成中の等式による型の輸送だけを除く。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
/-- 概要：二射影の指定比較同型は各脚の指定同型の端点の輸送。
方針：構成を展開し等式による輸送の HEq を使う。
規約：元の指定同型の値を保持する。
使われ方：native な可換性と指定 path の最終整合。 -/
lemma catPullbackConeFstIso_heq (p : A ⟶ C) (q : B ⟶ C) :
    HEq (catPullbackConeFstIso p q)
      ((catPullbackConeLegSectionIso p q (AsSmall.up.obj WalkingCospan.left)).postcomp
        (equivalencePathReplacementProjection p)) := by
  simp only [catPullbackConeFstIso, Eq.mp, _root_.id_eq]
  simp only [eqRec_heq_iff]
  rfl
/-- 概要：二射影の指定比較同型は各脚の指定同型の端点の輸送。
方針：構成を展開し等式による輸送の HEq を使う。
規約：元の指定同型の値を保持する。
使われ方：native な可換性と指定 path の最終整合。 -/
lemma catPullbackConeSndIso_heq (p : A ⟶ C) (q : B ⟶ C) :
    HEq (catPullbackConeSndIso p q)
      (catPullbackConeLegSectionIso p q (AsSmall.up.obj WalkingCospan.right)) := by
  simp only [catPullbackConeSndIso, _root_.id_eq, Eq.mp]
  rfl

end SerrePositivity.InfinityCategories.F2
