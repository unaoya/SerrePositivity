module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatPullbackConeSpecifiedComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatTriangleFacesEquality

/-!
概要：各脚の指定比較同型と元の三角形の同型の一致。
方針：指定円柱の側面と境界射の同定を合わせる。
規約：元の同型と一次単体を保持する。
使われ方：最初の比較三単体の指定同型の合成則。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
/-- 概要：指定比較同型は元の比較三角形の同型と型を含めて等しい。
方針：端点の輸送と三辺の回収が同型の値を保つことを使う。
規約：同型の存在だけでなく同じ値を追跡する。
使われ方：比較三単体の側面へ指定比較同型を代入する。 -/
lemma catPullbackConeLowerComparisonIso_heq (p : A ⟶ C) (q : B ⟶ C)
    (i : AsSmall.{u} WalkingCospan) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeLowerComparisonIso p q i)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTriangleIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyLowerTriangle (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeHomotopy p q)
        (ULift.up (ComposableArrows.mk₀ i)))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTriangleIso_of_faces_heq _ _ _ _ _ _ _
/-- 概要：指定比較同型は元の比較三角形の同型と型を含めて等しい。
方針：端点の輸送と三辺の回収が同型の値を保つことを使う。
規約：同型の存在だけでなく同じ値を追跡する。
使われ方：比較三単体の側面へ指定比較同型を代入する。 -/
lemma catPullbackConeUpperComparisonIso_heq (p : A ⟶ C) (q : B ⟶ C)
    (i : AsSmall.{u} WalkingCospan) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeUpperComparisonIso p q i)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTriangleIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyUpperTriangle (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeHomotopy p q)
        (ULift.up (ComposableArrows.mk₀ i)))) :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTriangleIso_of_faces_heq _ _ _ _ _ _ _)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
