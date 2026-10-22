module

public import SerrePositivity.InfinityCategories.F2.FunctorTrianglePointedLongWitness

/-!
概要：元の指定三角形の相対頂点比較を、同じ三角形を引数にして保持する。
方針：元の三辺・全三角形から既存の同じ指定比較へ直接渡す。
規約：比較を選び直さない。使われ方：全係数の制限と共通全空間上の指定比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 元の指定三角形から得た、元の三 native 作用の同じ相対頂点比較。 -/
def functorTriangleRelativeComparison {B : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
    {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
    (T : FunctorCompositionTriangle a b c) :=
  unstraighteningTriangleRelativeVertexIso F G J
    (coherentVertexOfHomotopy a) (coherentVertexOfHomotopy b) (coherentVertexOfHomotopy c)
    (coherentTriangleOfFunctorTriangle T).diagram (coherentTriangleOfFunctorTriangle T).first
    (coherentTriangleOfFunctorTriangle T).second (coherentTriangleOfFunctorTriangle T).long

end SerrePositivity.InfinityCategories.F2
