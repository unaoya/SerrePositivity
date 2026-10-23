module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTransformationTriangleSmall
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentFunctorTriangle

/-!
概要：元の指定合成三角形から、小さい全空間の同じ長辺・二辺合成の比較を取り出す。
方針：元の全三角形をそのまま縮小した作用比較へ渡す。
規約：三辺・二単体・指定比較を選び直さない。使われ方：native 模型側の正方形 hu。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 元の指定三角形の長辺と二辺の実合成の、元の縮小作用による同じ比較。 -/
def functorTriangleSmallTotalActionIso {B : SSet.{u}} [Quasicategory B]
    {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
    (T : FunctorCompositionTriangle a b d) :
    FunctorIso (coherentTransformationTotalMap F J (coherentVertexOfHomotopy d))
      (coherentTransformationTotalMap F G (coherentVertexOfHomotopy a) ≫
        coherentTransformationTotalMap G J (coherentVertexOfHomotopy b)) :=
  coherentTransformationTriangleSmallIso F G J (coherentVertexOfHomotopy a)
    (coherentVertexOfHomotopy b) (coherentTriangleOfFunctorTriangle T)

end SerrePositivity.InfinityCategories.F2
