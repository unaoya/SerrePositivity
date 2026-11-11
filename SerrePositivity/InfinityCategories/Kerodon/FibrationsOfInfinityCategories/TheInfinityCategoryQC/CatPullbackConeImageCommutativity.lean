module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatPullbackConeImageTriangles

/-!
概要：native な可換性と置換後の中心への二脚の比較の整合。
方針：左右の三角形の整合式から中心の指定比較同型を消去する。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
/-- 概要：native な可換性と置換後の中心への二脚の比較の整合。
方針：左右の三角形の整合式から中心の指定比較同型を消去する。
規約：元の指定同型の値を保持する。
使われ方：二射影の指定比較と指定 path の整合。 -/
lemma catPullbackConeImageIso_commutativity (p : A ⟶ C) (q : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeNativeCommutativity p q ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeRightImageIso p q =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeLeftImageIso p q := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeNativeCommutativity
  rw [Iso.trans_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeRightImageIso_triangle,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeLeftImageIso_triangle, Iso.symm_self_id_assoc]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
