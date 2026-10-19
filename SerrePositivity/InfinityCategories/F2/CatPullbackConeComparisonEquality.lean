module

public import SerrePositivity.InfinityCategories.F2.CatPullbackConeSpecifiedComparison
public import SerrePositivity.InfinityCategories.F2.CatTriangleFacesEquality

/-!
概要：各脚の指定比較同型と元の三角形の同型の一致。
方針：指定円柱の側面と境界射の同定を合わせる。
規約：元の同型と一次単体を保持する。
使われ方：最初の比較三単体の指定同型の合成則。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
/-- 概要：指定比較同型は元の比較三角形の同型と型を含めて等しい。
方針：端点の輸送と三辺の回収が同型の値を保つことを使う。
規約：同型の存在だけでなく同じ値を追跡する。
使われ方：比較三単体の側面へ指定比較同型を代入する。 -/
lemma catPullbackConeLowerComparisonIso_heq (p : A ⟶ C) (q : B ⟶ C)
    (i : AsSmall.{u} WalkingCospan) :
    HEq (catPullbackConeLowerComparisonIso p q i)
      (catInfinityTriangleIso (coneHomotopyLowerTriangle (catPullbackConeHomotopy p q)
        (ULift.up (ComposableArrows.mk₀ i)))) :=
  catInfinityTriangleIso_of_faces_heq _ _ _ _ _ _ _
/-- 概要：指定比較同型は元の比較三角形の同型と型を含めて等しい。
方針：端点の輸送と三辺の回収が同型の値を保つことを使う。
規約：同型の存在だけでなく同じ値を追跡する。
使われ方：比較三単体の側面へ指定比較同型を代入する。 -/
lemma catPullbackConeUpperComparisonIso_heq (p : A ⟶ C) (q : B ⟶ C)
    (i : AsSmall.{u} WalkingCospan) :
    HEq (catPullbackConeUpperComparisonIso p q i)
      (catInfinityTriangleIso (coneHomotopyUpperTriangle (catPullbackConeHomotopy p q)
        (ULift.up (ComposableArrows.mk₀ i)))) :=
  (functorIsoOfEq_heq _ _ _).trans (catInfinityTriangleIso_of_faces_heq _ _ _ _ _ _ _)

end SerrePositivity.InfinityCategories.F2
