module

public import SerrePositivity.InfinityCategories.F2.CatPullbackMiddleTetrahedronRelation
public import SerrePositivity.InfinityCategories.F2.CatPullbackLastTetrahedronDiagonalEdges
public import SerrePositivity.InfinityCategories.F2.CatPullbackConeLegTriangleEquality

/-!
概要：最後の比較三単体の指定同型の合成関係。
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
/-- 概要：最後の四面の指定同型の合成は元の錐の三角形と下側の比較に一致。
方針：元の三角形と六辺を揃えて四面の合成則を使う。
規約：共有面の同型の値を変更しない。
使われ方：三つの関係を合わせて各脚の比較の整合式を導く。 -/
lemma catPullbackLastTetrahedron_relation (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    catPullbackSecondInteriorIso p q f ≪≫
        (catPullbackDiagramLowerComparisonIso p q f).precomp
          (show catPullback p q ⟶ ((catPullbackDiagram p q).obj i).obj from
            catPullbackConeFunctorLeg p q i) =
      catPullbackConeLowerComparisonIso p q j ≪≫
        (catPullbackConeLegTriangleIso p q f).postcomp
          ((catPullbackReplacementNatTrans p q).app j) := by
  exact catInfinityTetrahedronIso_square_of_edges
    (catPullbackConeFunctorLeg p q i) ((catPullbackDiagram p q).map f)
    ((catPullbackReplacementNatTrans p q).app j) (catPullbackConeFunctorLeg p q j)
    (catPullbackDiagramDiagonal p q f) (catPullbackConeDiagonal p q j)
    (catPullbackConeTetrahedron p q f 2)
    (catPullbackLastTetrahedron_edge01 p q f) (catPullbackLastTetrahedron_edge12 p q f)
    (catPullbackLastTetrahedron_edge23 p q f) (catPullbackLastTetrahedron_edge02 p q f)
    (catPullbackLastTetrahedron_edge13 p q f) (catPullbackLastTetrahedron_edge03 p q f)
    _ _ _ _
    ((catPullbackSecondInteriorIso_heq p q f).trans
      (catInfinityTriangleIso_heq (catPullbackConeTetrahedron_glue_last p q f)))
    ((catPullbackDiagramLowerComparisonIso_heq p q f).trans
      (catInfinityTriangleIso_heq (catPullbackDiagramLowerTriangle_tetrahedron p q f)).symm)
    ((catPullbackConeLowerComparisonIso_heq p q j).trans
      (catInfinityTriangleIso_heq (catPullbackConeTetrahedron_lower_long p q f)).symm)
    ((catPullbackConeLegTriangleIso_heq p q f).trans
      (catInfinityTriangleIso_heq (catPullbackConeTetrahedron_last p q f)).symm)

end SerrePositivity.InfinityCategories.F2
