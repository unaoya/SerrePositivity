module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTriangleEdgeComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTriangleCanonicalPrisms
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorHomotopyPrismSpecifiedNaturality

/-!
概要：元の全三角形の右辺の指定比較に、始点も動く prism 比較の指定自然性を適用する。
方針：同じ全三角形比較の像を、元の実右辺と指定右辺の証拠型で読む。
規約：全係数・元の指定同型を保持。使われ方：終点比較を二辺の指定始域比較へ結ぶ。
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
local notation "base" => (Δ[1] ◁ p) ≫ functorSimplexDiagram (curry b.h)

/-- 元の全三角形の同じ指定比較を、同じ二つの実右辺の証拠型で保持する。 -/
def FunctorTrianglePointedWitness.rightPrismComparison :
    VertexIso
      (relativeFunctorVertex pointedSpaceProjection base
        w.secondWitness.extension w.secondWitness.over)
      (relativeFunctorVertex pointedSpaceProjection base
        (z).secondWitness.extension (z).secondWitness.over) :=
  w.prismComparison b 0 T.face_zero hi

/-- 右辺の元の指定比較の始点像に native 第二作用を施した、同じ指定値。 -/
def FunctorTrianglePointedWitness.rightNativeComparison :=
  functorHomotopyPrismNativeComparison b p w.middle (z).middle
    w.middle_projection (z).middle_projection w.secondWitness (z).secondWitness
    (w.rightPrismComparison hi)

/-- 右辺の元の指定比較を、同じ元の全実終点で評価した値。 -/
def FunctorTrianglePointedWitness.rightActualComparison :=
  functorHomotopyPrismActualComparison b p w.middle (z).middle
    w.secondWitness (z).secondWitness (w.rightPrismComparison hi)

/-- 元の全三角形の右辺比較は、同じ元の二始域比較と型付きの可換正方形を作る。 -/
lemma FunctorTrianglePointedWitness.right_specified_naturality :
    w.rightNativeComparison hi ≪≫
      functorHomotopySourceEndpointIso b p (z).middle (z).middle_projection (z).secondWitness =
      functorHomotopySourceEndpointIso b p w.middle w.middle_projection w.secondWitness ≪≫
        w.rightActualComparison hi :=
  functorHomotopyPrismSpecified_naturality b p w.middle (z).middle
    w.middle_projection (z).middle_projection w.secondWitness (z).secondWitness
    (w.rightPrismComparison hi)

end SerrePositivity.InfinityCategories.F2
