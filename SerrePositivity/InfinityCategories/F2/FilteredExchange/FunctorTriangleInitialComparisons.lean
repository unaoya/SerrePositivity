module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTriangleInitialNativeComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTriangleCanonicalPrisms
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorHomotopyPrismSpecifiedNaturality

/-!
概要：元の全三角形比較の第一辺・長辺の像を、同じ実証拠の型で保持する。
方針：元の全族の指定辺比較を元の二 prism 証拠として読み、同じ native 始点・実終点へ写す。
規約：全係数・元の指定値を保持。使われ方：二辺の比較と元の指定三角形比較の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  {T : FunctorCompositionTriangle a b c} {p : C ⟶ B} {s : C ⟶ leftUnstraightening F}
  (w : FunctorTrianglePointedWitness T p s) (hi : s ≫ leftUnstraighteningProjection F = p)
local notation "z" => functorTrianglePointedCanonicalWitness T p s hi

/-- 元の同じ全三角形比較の第一辺の像を、元の二つの実第一辺の証拠型で保持する。 -/
def FunctorTrianglePointedWitness.firstPrismComparison :
    VertexIso (relativeFunctorVertex pointedSpaceProjection
      ((Δ[1] ◁ p) ≫ functorSimplexDiagram (curry a.h)) w.firstWitness.extension w.firstWitness.over)
      (relativeFunctorVertex pointedSpaceProjection ((Δ[1] ◁ p) ≫ functorSimplexDiagram (curry a.h))
        (z).firstWitness.extension (z).firstWitness.over) :=
  w.prismComparison a 2 T.face_two hi

/-- 元の同じ全三角形比較の長辺の像を、元の二つの実長辺の証拠型で保持する。 -/
def FunctorTrianglePointedWitness.longPrismComparison :
    VertexIso (relativeFunctorVertex pointedSpaceProjection
      ((Δ[1] ◁ p) ≫ functorSimplexDiagram (curry c.h)) w.longWitness.extension w.longWitness.over)
      (relativeFunctorVertex pointedSpaceProjection ((Δ[1] ◁ p) ≫ functorSimplexDiagram (curry c.h))
        (z).longWitness.extension (z).longWitness.over) :=
  w.prismComparison c 1 T.face_one hi

/-- 元の第一辺の指定比較の native 始点像。 -/
def FunctorTrianglePointedWitness.firstNativeComparison :=
  functorHomotopyPrismNativeComparison a p s s hi hi w.firstWitness (z).firstWitness
    (w.firstPrismComparison hi)

/-- 元の長辺の指定比較の native 始点像。 -/
def FunctorTrianglePointedWitness.longNativeComparison :=
  functorHomotopyPrismNativeComparison c p s s hi hi w.longWitness (z).longWitness
    (w.longPrismComparison hi)

/-- 元の第一辺の指定比較を、同じ元の実中間頂点で評価した値。 -/
def FunctorTrianglePointedWitness.firstActualComparison :=
  functorHomotopyPrismActualComparison a p s s w.firstWitness (z).firstWitness
    (w.firstPrismComparison hi)

/-- 元の長辺の指定比較を、同じ元の実終点で評価した値。 -/
def FunctorTrianglePointedWitness.longActualComparison :=
  functorHomotopyPrismActualComparison c p s s w.longWitness (z).longWitness
    (w.longPrismComparison hi)

end SerrePositivity.InfinityCategories.F2
