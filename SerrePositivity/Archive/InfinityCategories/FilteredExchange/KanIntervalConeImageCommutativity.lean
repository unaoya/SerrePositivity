module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanIntervalConeImageTriangles

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

variable {X Y Z : KanObject.{u}}
/-- 概要：native な可換性と置換後の中心への二脚の比較の整合。
方針：左右の三角形の整合式から中心の指定比較同型を消去する。
規約：元の指定同型の値を保持する。
使われ方：二射影の指定比較と指定 path の整合。 -/
lemma intervalPullbackConeImageIso_commutativity (f : X ⟶ Y) (g : Z ⟶ Y) :
    intervalPullbackConeNativeCommutativity f g ≪≫ intervalPullbackConeRightImageIso f g =
      intervalPullbackConeLeftImageIso f g := by
  unfold intervalPullbackConeNativeCommutativity
  rw [Iso.trans_assoc, intervalPullbackConeRightImageIso_triangle,
    ← intervalPullbackConeLeftImageIso_triangle, Iso.symm_self_id_assoc]

end SerrePositivity.InfinityCategories.F2
