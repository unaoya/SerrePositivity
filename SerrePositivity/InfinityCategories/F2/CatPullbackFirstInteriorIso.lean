module

public import SerrePositivity.InfinityCategories.F2.CatPullbackFirstTetrahedronDiagonalEdges
public import SerrePositivity.InfinityCategories.F2.TetrahedronEdgeFaces
public import SerrePositivity.InfinityCategories.F2.CatTriangleFacesEquality

/-!
概要：最初と中央の比較三単体の共有面からの指定内部同型。
方針：全錐の同じ指定比較円柱とその面の同定を使う。
規約：共有面の同型を選び直さず元の単体から読む。
使われ方：二射影の指定比較同型と指定 path の整合の証明。
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
/-- 概要：同じ対角関手と置換後の図式の射を結ぶ指定同型。
方針：元の三角形の同型と境界関手を揃えて四面の合成則を使う。
規約：指定同型の存在でなく元の値と合成の等式を保持する。
使われ方：三つの比較三単体の関係から二脚の比較の整合を導く。 -/
def catPullbackFirstInteriorIso (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    FunctorIso (catPullbackConeDiagonal p q j)
      (catPullbackConeDiagonal p q i ≫ (catPullbackReplacementDiagram p q).map f) :=
  catInfinityTriangleIso_of_faces _ _ _
    (CatInfinity.δ 1 (catPullbackConeTetrahedron p q f 0))
    ((tetrahedronEdge02_eq _).trans (catPullbackFirstTetrahedron_edge02 p q f))
    ((tetrahedronEdge23_eq _).trans (catPullbackFirstTetrahedron_edge23 p q f))
    ((tetrahedronEdge03_eq _).trans (catPullbackFirstTetrahedron_edge03 p q f))
/-- 概要：指定内部同型は元の共有面の同型と型を含めて等しい。
方針：元の三角形の同型と境界関手を揃えて四面の合成則を使う。
規約：指定同型の存在でなく元の値と合成の等式を保持する。
使われ方：三つの比較三単体の関係から二脚の比較の整合を導く。 -/
lemma catPullbackFirstInteriorIso_heq (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    HEq (catPullbackFirstInteriorIso p q f)
      (catInfinityTriangleIso (CatInfinity.δ 1 (catPullbackConeTetrahedron p q f 0))) :=
  catInfinityTriangleIso_of_faces_heq _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.F2
