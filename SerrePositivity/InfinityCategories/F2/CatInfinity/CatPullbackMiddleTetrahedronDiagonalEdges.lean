module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackMiddleTetrahedronBaseEdges
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackFirstTetrahedronDiagonalEdges
public import SerrePositivity.InfinityCategories.F2.CatInfinity.TetrahedronEdgeFaces

/-!
概要：中央の比較三単体の指定境界関手。
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
/-- 概要：比較三単体の辺 01 は指定境界関手の coherent 辺。
方針：側面の三角形と共有面の一致を使う。
規約：一次単体の厳密な等式。
使われ方：六つの境界関手を固定して四面の合成則を適用する。 -/
lemma catPullbackMiddleTetrahedron_edge01 (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    CatInfinity.δ 2 (CatInfinity.δ 2 (catPullbackConeTetrahedron p q f 1)) =
      (coherentNerveEdge (catPullbackConeFunctorLeg p q i)).edge :=
  (tetrahedronEdge01_eq _).symm.trans
    ((congrArg (CatInfinity.δ 2) (catPullbackConeTetrahedron_lower_first p q f)).trans
      (catPullbackConeLowerTriangle_two p q i))
/-- 概要：比較三単体の辺 02 は指定境界関手の coherent 辺。
方針：側面の三角形と共有面の一致を使う。
規約：一次単体の厳密な等式。
使われ方：六つの境界関手を固定して四面の合成則を適用する。 -/
lemma catPullbackMiddleTetrahedron_edge02 (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    CatInfinity.δ 1 (CatInfinity.δ 3 (catPullbackConeTetrahedron p q f 1)) =
      (coherentNerveEdge (catPullbackConeDiagonal p q i)).edge :=
  (congrArg (CatInfinity.δ 1) (catPullbackConeTetrahedron_lower_first p q f)).trans
    (catPullbackConeLowerTriangle_one p q i)
/-- 概要：比較三単体の辺 03 は指定境界関手の coherent 辺。
方針：側面の三角形と共有面の一致を使う。
規約：一次単体の厳密な等式。
使われ方：六つの境界関手を固定して四面の合成則を適用する。 -/
lemma catPullbackMiddleTetrahedron_edge03 (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    CatInfinity.δ 1 (CatInfinity.δ 2 (catPullbackConeTetrahedron p q f 1)) =
      (coherentNerveEdge (catPullbackConeDiagonal p q j)).edge :=
  (tetrahedronEdge03_eq _).symm.trans
    ((congrArg (CatInfinity.δ 1) (catPullbackConeTetrahedron_glue_first p q f)).symm.trans
      ((tetrahedronEdge03_eq _).trans (catPullbackFirstTetrahedron_edge03 p q f)))

end SerrePositivity.InfinityCategories.F2
