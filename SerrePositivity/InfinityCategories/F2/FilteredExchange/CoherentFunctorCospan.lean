module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentFunctorTriangle
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanConePointwise

/-!
概要：元の共通対角辺を持つ二つの関手三角形を coherent な cospan 錐へ接続する。
方針：四辺と二つの全三角形をそのまま変換空間の表示へ移す。
規約：共通対角円柱を保持。使われ方：部分極限の貼り合わせと既存の filtered 比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  {F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F X} {b : SSet.Homotopy F Y}
  {f : SSet.Homotopy X Z} {g : SSet.Homotopy Y Z} {d : SSet.Homotopy F Z}
  (L : FunctorCompositionTriangle a f d) (R : FunctorCompositionTriangle b g d)

/-- 元の四辺・共通対角円柱・二つの全三角形を持つ coherent な cospan 錐の表示。 -/
def coherentCospanOfFunctorTriangles : CoherentTransformationCospanCone F X Y Z where
  toLeft := coherentVertexOfHomotopy a
  toRight := coherentVertexOfHomotopy b
  fromLeft := coherentVertexOfHomotopy f
  fromRight := coherentVertexOfHomotopy g
  leftTriangle := coherentTriangleOfFunctorTriangle L
  rightTriangle := coherentTriangleOfFunctorTriangle R
  diagonal_eq := rfl

/-- 元の左三角形の一点評価は、元の左関手二単体の全評価そのもの。 -/
lemma coherentCospanOfFunctorTriangles_left_point (v : B _⦋0⦌) :
    coherentTransformationPointDiagram
      (coherentCospanOfFunctorTriangles L R).leftTriangle.diagram (ULift.up v) =
      L.diagram ≫ evaluateFunctorAt (ULift.up v) := coherentTriangleOfFunctorTriangle_point L _

/-- 元の右三角形の一点評価は、元の右関手二単体の全評価そのもの。 -/
lemma coherentCospanOfFunctorTriangles_right_point (v : B _⦋0⦌) :
    coherentTransformationPointDiagram
      (coherentCospanOfFunctorTriangles L R).rightTriangle.diagram (ULift.up v) =
      R.diagram ≫ evaluateFunctorAt (ULift.up v) := coherentTriangleOfFunctorTriangle_point R _

end SerrePositivity.InfinityCategories.F2
