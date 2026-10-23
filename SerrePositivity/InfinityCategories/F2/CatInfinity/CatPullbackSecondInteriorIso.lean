module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackMiddleTetrahedronDiagonalEdges
public import SerrePositivity.InfinityCategories.F2.CatInfinity.TetrahedronEdgeFaces
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatTriangleFacesEquality

/-!
概要：中央と最後の比較三単体の共有面からの指定内部同型。
方針：指定円柱の実際の三単体と共有面の式を使う。
規約：同型の存在でなく指定同型の合成の等式を保持する。
使われ方：二射影の指定比較同型と指定 path の照合。
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
/-- 概要：元の脚と図式側の対角射の合成へ向かう第二の指定内部同型。
方針：元の三角形と六辺を揃えて四面の合成則を使う。
規約：共有面の同型の値を変更しない。
使われ方：三つの関係を合わせて各脚の比較の整合式を導く。 -/
def catPullbackSecondInteriorIso (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    FunctorIso (catPullbackConeDiagonal p q j)
      (catPullbackConeFunctorLeg p q i ≫ catPullbackDiagramDiagonal p q f) :=
  catInfinityTriangleIso_of_faces _ _ _
    (CatInfinity.δ 2 (catPullbackConeTetrahedron p q f 1))
    (catPullbackMiddleTetrahedron_edge01 p q f)
    ((tetrahedronEdge13_eq _).trans (catPullbackMiddleTetrahedron_edge13 p q f))
    (catPullbackMiddleTetrahedron_edge03 p q f)
/-- 概要：第二の指定内部同型は元の共有面の同型と型を含めて等しい。
方針：元の三角形と六辺を揃えて四面の合成則を使う。
規約：共有面の同型の値を変更しない。
使われ方：三つの関係を合わせて各脚の比較の整合式を導く。 -/
lemma catPullbackSecondInteriorIso_heq (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    HEq (catPullbackSecondInteriorIso p q f)
      (catInfinityTriangleIso (CatInfinity.δ 2 (catPullbackConeTetrahedron p q f 1))) :=
  catInfinityTriangleIso_of_faces_heq _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.F2
