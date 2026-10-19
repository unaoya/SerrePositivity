module

public import SerrePositivity.InfinityCategories.F2.CatPullbackConeImageTriangles

/-!
概要：native な可換性と置換後の中心への二脚の比較の整合。
方針：左右の三角形の整合式から中心の指定比較同型を消去する。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
/-- 概要：native な可換性と置換後の中心への二脚の比較の整合。
方針：左右の三角形の整合式から中心の指定比較同型を消去する。
規約：元の指定同型の値を保持する。
使われ方：二射影の指定比較と指定 path の整合。 -/
lemma catPullbackConeImageIso_commutativity (p : A ⟶ C) (q : B ⟶ C) :
    catPullbackConeNativeCommutativity p q ≪≫ catPullbackConeRightImageIso p q =
      catPullbackConeLeftImageIso p q := by
  unfold catPullbackConeNativeCommutativity
  rw [Iso.trans_assoc, catPullbackConeRightImageIso_triangle,
    ← catPullbackConeLeftImageIso_triangle, Iso.symm_self_id_assoc]

end SerrePositivity.InfinityCategories.F2
