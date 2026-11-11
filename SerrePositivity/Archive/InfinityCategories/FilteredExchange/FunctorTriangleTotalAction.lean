module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleRelativeComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.UnstraighteningTriangleVertex

/-!
概要：元の全三角形の指定比較を、同じ三つの全空間実射の比較として保持する。
方針：元の相対比較を同じ包含で忘れる既存の全空間比較を使う。
規約：三角形・三辺を選び直さない。使われ方：単位表現との後合成の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 元の指定三角形から得る、元の長作用と元の二作用の合成の同じ全空間比較。 -/
def functorTriangleTotalActionIso {B : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
    {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
    (T : FunctorCompositionTriangle a b c) :
    FunctorIso (leftUnstraighteningMappingVertexMap F J (coherentVertexOfHomotopy c)).val
      ((leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)).val ≫
        (leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b)).val) :=
  unstraighteningTriangleVertexIso F G J
    (coherentVertexOfHomotopy a) (coherentVertexOfHomotopy b) (coherentVertexOfHomotopy c)
    (coherentTriangleOfFunctorTriangle T).diagram (coherentTriangleOfFunctorTriangle T).first
    (coherentTriangleOfFunctorTriangle T).second (coherentTriangleOfFunctorTriangle T).long

end SerrePositivity.InfinityCategories.F2
