module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackDiagramLowerTriangle
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatTriangleFacesEquality

/-!
概要：図式側の指定上下三角形の比較同型。
方針：同じ指定円柱の面と六辺の回収を使う。
規約：元の単体と指定同型を選び直さない。
使われ方：中央と最後の比較三単体の合成関係。
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
/-- 概要：上側の指定三角形は対角射と切断・置換後の射の合成の同型。
方針：同じ対角関手を通る元の三角形の同型を使う。
規約：指定辺の類を保持する。
使われ方：三つの比較三単体の合成関係を合わせる。 -/
def catPullbackDiagramUpperComparisonIso (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    FunctorIso (catPullbackDiagramDiagonal p q f)
      ((catPullbackReplacementNatTrans p q).app i ≫ (catPullbackReplacementDiagram p q).map f) :=
  catInfinityTriangleIso_of_faces _ _ _ (catPullbackDiagramUpperTriangle p q f)
    (catPullbackDiagramUpperTriangle_two p q f) (catPullbackDiagramUpperTriangle_zero p q f)
    (catPullbackDiagramUpperTriangle_one p q f)
/-- 概要：下側の指定三角形は対角射と元の射・切断の合成の同型。
方針：同じ対角関手を通る元の三角形の同型を使う。
規約：指定辺の類を保持する。
使われ方：三つの比較三単体の合成関係を合わせる。 -/
def catPullbackDiagramLowerComparisonIso (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    FunctorIso (catPullbackDiagramDiagonal p q f)
      ((catPullbackDiagram p q).map f ≫ (catPullbackReplacementNatTrans p q).app j) :=
  catInfinityTriangleIso_of_faces _ _ _ (catPullbackDiagramLowerTriangle p q f)
    (catPullbackDiagramLowerTriangle_two p q f) (catPullbackDiagramLowerTriangle_zero p q f)
    (catPullbackDiagramLowerTriangle_one p q f)
/-- 概要：上側の指定同型は元の二単体の同型と型を含めて等しい。
方針：同じ対角関手を通る元の三角形の同型を使う。
規約：指定辺の類を保持する。
使われ方：三つの比較三単体の合成関係を合わせる。 -/
lemma catPullbackDiagramUpperComparisonIso_heq (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    HEq (catPullbackDiagramUpperComparisonIso p q f)
      (catInfinityTriangleIso (catPullbackDiagramUpperTriangle p q f)) :=
  catInfinityTriangleIso_of_faces_heq _ _ _ _ _ _ _
/-- 概要：下側の指定同型は元の二単体の同型と型を含めて等しい。
方針：同じ対角関手を通る元の三角形の同型を使う。
規約：指定辺の類を保持する。
使われ方：三つの比較三単体の合成関係を合わせる。 -/
lemma catPullbackDiagramLowerComparisonIso_heq (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    HEq (catPullbackDiagramLowerComparisonIso p q f)
      (catInfinityTriangleIso (catPullbackDiagramLowerTriangle p q f)) :=
  catInfinityTriangleIso_of_faces_heq _ _ _ _ _ _ _
/-- 概要：図式の比較正方形の指定同型。
方針：同じ対角関手を通る元の三角形の同型を使う。
規約：指定辺の類を保持する。
使われ方：三つの比較三単体の合成関係を合わせる。 -/
def catPullbackDiagramComparisonIso (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    FunctorIso ((catPullbackDiagram p q).map f ≫ (catPullbackReplacementNatTrans p q).app j)
      ((catPullbackReplacementNatTrans p q).app i ≫ (catPullbackReplacementDiagram p q).map f) :=
  (catPullbackDiagramLowerComparisonIso p q f).symm ≪≫ catPullbackDiagramUpperComparisonIso p q f

end SerrePositivity.InfinityCategories.F2
