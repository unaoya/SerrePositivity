module

public import SerrePositivity.InfinityCategories.F2.CatPullbackReplacementTriangleIso
public import SerrePositivity.InfinityCategories.F2.CatPullbackFirstInteriorIso
public import SerrePositivity.InfinityCategories.F2.CatPullbackConeComparisonEquality
public import SerrePositivity.InfinityCategories.F2.CatTetrahedronNamedIsoSquare

/-!
概要：最初の比較三単体の指定比較同型の合成関係。
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
/-- 概要：上側の二脚の指定比較と置換後の三角形は共有面の同型を介して可換。
方針：元の三角形の同型と境界関手を揃えて四面の合成則を使う。
規約：指定同型の存在でなく元の値と合成の等式を保持する。
使われ方：三つの比較三単体の関係から二脚の比較の整合を導く。 -/
lemma catPullbackFirstTetrahedron_relation (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    catPullbackConeUpperComparisonIso p q j ≪≫
        (catPullbackReplacementTriangleIso p q f).precomp
          (𝟙 (catPullback p q)) =
      catPullbackFirstInteriorIso p q f ≪≫
        (catPullbackConeUpperComparisonIso p q i).postcomp
          ((catPullbackReplacementDiagram p q).map f) := by
  exact catInfinityTetrahedronIso_square_of_edges
    (𝟙 (catPullbackObject p q)) ((catPullbackReplacementOrdinaryCone p q).π.app i)
    ((catPullbackReplacementDiagram p q).map f) (catPullbackConeDiagonal p q i)
    ((catPullbackReplacementOrdinaryCone p q).π.app j) (catPullbackConeDiagonal p q j)
    (catPullbackConeTetrahedron p q f 0)
    (catPullbackFirstTetrahedron_edge01 p q f) (catPullbackFirstTetrahedron_edge12 p q f)
    (catPullbackFirstTetrahedron_edge23 p q f) (catPullbackFirstTetrahedron_edge02 p q f)
    (catPullbackFirstTetrahedron_edge13 p q f) (catPullbackFirstTetrahedron_edge03 p q f)
    _ _ _ _
    ((catPullbackConeUpperComparisonIso_heq p q j).trans
      (catInfinityTriangleIso_heq (catPullbackConeTetrahedron_upper_long p q f)).symm)
    ((catPullbackReplacementTriangleIso_heq p q f).trans
      (catInfinityTriangleIso_heq (catPullbackConeTetrahedron_first p q f)).symm)
    (catPullbackFirstInteriorIso_heq p q f)
    ((catPullbackConeUpperComparisonIso_heq p q i).trans
      (catInfinityTriangleIso_heq (catPullbackConeTetrahedron_upper_first p q f)).symm)

end SerrePositivity.InfinityCategories.F2
