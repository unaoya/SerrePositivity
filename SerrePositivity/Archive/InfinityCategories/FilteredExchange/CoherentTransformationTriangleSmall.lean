module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTransformationTriangleRelative
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SmallUnstraighteningFunctorIso
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTransformationVertexTriangle
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTransformationTotalMap

/-!
概要：元の coherent 三角形の指定比較を元の小さい全空間上に移す。
方針：同じ三角形の比較同型を縮小し、縮小の合成式で終点を揃える。
規約：元の三角形を保持。使われ方：左右二三角形からの指定可換性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：指定三角形の小さい長辺の作用は元の小さい二辺の合成と同型。
方針：元の全空間比較と縮小の関手性。
規約：指定三角形と三辺を保持。使われ方：元の cospan 錐の可換同型。 -/
def coherentTransformationTriangleSmallIso {B : SSet.{u}} [Quasicategory B]
    (F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
    (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
    (T : CoherentTransformationVertexTriangle F G J x y) :
    FunctorIso (coherentTransformationTotalMap F J T.diagonal)
      (coherentTransformationTotalMap F G x ≫ coherentTransformationTotalMap G J y) := by
  exact (coherentTransformationTriangleRelativeIso F G J x y T).map
    (vertexFiberι ((ihom (smallLeftUnstraightening F)).map (smallLeftUnstraighteningProjection J))
      (functorVertex (smallLeftUnstraighteningProjection F)))

end SerrePositivity.InfinityCategories.F2
