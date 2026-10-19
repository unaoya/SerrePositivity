module

public import SerrePositivity.InfinityCategories.F2.CatPullbackConeLowerTriangle
public import SerrePositivity.InfinityCategories.F2.CatTriangleFaces
public import SerrePositivity.InfinityCategories.F2.FunctorIsoTransport

/-!
概要：同じ指定円柱の二つの三角形からの各脚の比較同型。
方針：共通の対角関手を読み戻し、上下の三角形の指定同型を合成する。
規約：各脚の比較を存在命題から個別に選択しない。
使われ方：二射影の比較同型と指定 path の整合を検証する入力。
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
/-- 概要：下側の指定三角形は対角関手と元の脚・切断の合成の同型。
方針：元の三辺を指定関手に合わせて三角形の同型を読む。
規約：同型の存在からの選択を新たに行わない。
使われ方：二脚の比較と native な可換性の同時の整合。 -/
def catPullbackConeLowerComparisonIso (p : A ⟶ C) (q : B ⟶ C)
    (i : AsSmall.{u} WalkingCospan) :
    FunctorIso (catPullbackConeDiagonal p q i)
      (catPullbackConeFunctorLeg p q i ≫ (catPullbackReplacementNatTrans p q).app i) :=
  catInfinityTriangleIso_of_faces _ _ _
    (coneHomotopyLowerTriangle (catPullbackConeHomotopy p q) (ULift.up (ComposableArrows.mk₀ i)))
    (catPullbackConeLowerTriangle_two p q i) (catPullbackConeLowerTriangle_zero p q i)
    (catPullbackConeLowerTriangle_one p q i)
/-- 概要：上側の指定三角形は対角関手と置換後の脚の同型。
方針：頂点の恒等関手との合成を等式で正規化する。
規約：同型の存在からの選択を新たに行わない。
使われ方：二脚の比較と native な可換性の同時の整合。 -/
def catPullbackConeUpperComparisonIso (p : A ⟶ C) (q : B ⟶ C)
    (i : AsSmall.{u} WalkingCospan) :
    FunctorIso (catPullbackConeDiagonal p q i)
      ((catPullbackReplacementOrdinaryCone p q).π.app i) :=
  functorIsoOfEq
    (catInfinityTriangleIso_of_faces (𝟙 (catPullbackObject p q)) _ _
      (coneHomotopyUpperTriangle (catPullbackConeHomotopy p q) (ULift.up (ComposableArrows.mk₀ i)))
      (catPullbackConeUpperTriangle_two p q i) (catPullbackConeUpperTriangle_zero p q i)
      (catPullbackConeUpperTriangle_one p q i)) rfl (Category.id_comp _)
/-- 概要：同じ指定円柱から各脚と切断の合成を置換後の脚に比較する。
方針：同じ対角関手を通る上下の指定三角形の同型を合成する。
規約：同型の存在からの選択を新たに行わない。
使われ方：二脚の比較と native な可換性の同時の整合。 -/
def catPullbackConeLegSectionIso (p : A ⟶ C) (q : B ⟶ C)
    (i : AsSmall.{u} WalkingCospan) :
    FunctorIso (catPullbackConeFunctorLeg p q i ≫ (catPullbackReplacementNatTrans p q).app i)
      ((catPullbackReplacementOrdinaryCone p q).π.app i) :=
  (catPullbackConeLowerComparisonIso p q i).symm ≪≫ catPullbackConeUpperComparisonIso p q i

end SerrePositivity.InfinityCategories.F2
