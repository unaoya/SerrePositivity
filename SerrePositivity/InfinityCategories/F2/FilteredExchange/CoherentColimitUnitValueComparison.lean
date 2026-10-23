module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitTriangles
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTriangleSequentialPostComparison

/-!
概要：元の単位正方形の指定比較を、共有対角を持つ元の下三角形・上三角形の比較から作る。
方針：元の下側の指定値の逆と元の上側の指定値を合成する。
規約：元の対角と二面を保持。使われ方：二三角形・指定 path を保つ全錐比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の単位正方形の全二面・同じ対角から得る、元の native 作用の指定比較。 -/
def coherentColimitUnitValueComparison (B : SSet.{u}) {C : SSet.{u + 1}}
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)
    (p : C ⟶ (SSet.uliftFunctor.{u + 1, u}).obj B)
    (x : (relativeFunctorSpace (leftUnstraighteningProjection F) p) _⦋0⦌) :=
  ((functorTriangleSequentialPostComparison (coherentColimitUnitLowerTriangle B H) p).app x).symm ≪≫
    (functorTriangleSequentialPostComparison (coherentColimitUnitUpperTriangle B H) p).app x

end SerrePositivity.InfinityCategories.F2
