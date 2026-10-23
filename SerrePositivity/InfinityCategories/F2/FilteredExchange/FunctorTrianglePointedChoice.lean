module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTrianglePointedLift

/-!
概要：元の指定三角形の実持ち上げを、始点固定の同じ全延長空間の頂点にする。
方針：元の初期頂点の等式を全初期面の等式へ戻す。
規約：元の実延長を保持。使われ方：固定始点を持つ三単体の面比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d)

/-- 元の指定三角形の持ち上げは、全初期面で同じ pointed 始点を保つ。 -/
lemma functorTrianglePointedLift_start :
    (scaffoldFirstVertex 2 ▷ leftUnstraightening F) ≫ functorTrianglePointedLift T =
      leftUnstraighteningSimplexStart F := by
  rw [scaffoldFirstVertex_whiskerRight, Category.assoc, functorTrianglePointedLift_initial]
  rfl

/-- 元の指定三角形比較の実持ち上げを、同じ全初期値固定の選択空間へ入れる。 -/
def functorTrianglePointedChoiceVertex
    (h₀ : simplexPrismVertex 2 0 B ≫ functorSimplexDiagram T.diagram = F) :
    (leftUnstraighteningSimplexChoiceSpace F 2 (functorSimplexDiagram T.diagram) h₀) _⦋0⦌ :=
  relativeFunctorExtensionSpaceVertexEquiv pointedSpaceProjection
    ((Δ[2] ◁ leftUnstraighteningProjection F) ≫ functorSimplexDiagram T.diagram)
    (scaffoldFirstVertex 2 ▷ leftUnstraightening F) (leftUnstraighteningSimplexStart F)
    (leftUnstraighteningSimplexStart_projection F 2 _ h₀)
    ⟨functorTrianglePointedLift T, functorTrianglePointedLift_projection T,
      functorTrianglePointedLift_start T⟩

/-- 選択空間へ入れた頂点は、同じ元の全持ち上げを厳密に表す。 -/
lemma functorTrianglePointedChoiceVertex_value
    (h₀ : simplexPrismVertex 2 0 B ≫ functorSimplexDiagram T.diagram = F) :
    ((functorTrianglePointedChoiceVertex T h₀).val).val =
      functorVertex (functorTrianglePointedLift T) := rfl

end SerrePositivity.InfinityCategories.F2
