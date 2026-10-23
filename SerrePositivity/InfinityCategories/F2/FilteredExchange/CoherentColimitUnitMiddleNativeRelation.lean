module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitMiddleBoundary

/-!
概要：元の単位三単体の四面の指定比較を、元の三角形のまま厳密な合成関係へ戻す。
方針：元の外側面と同じ内部面の等式を用い、比較も三角形も再選択しない。
規約：元の三単体を保持。使われ方：四面の指定比較の可換性の具体化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d)

local notation "K" => coherentColimitUnitPointedTetrahedronChoice B T 1
local notation "p" => fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F
local notation "x₀" => relativeFunctorVertex (leftUnstraighteningProjection F) p
  (fst (leftUnstraightening F) K) rfl

/-- 元の第 1 単位三単体の全四面の指定比較は、元の六辺を保って厳密な合成関係を満たす。 -/
lemma coherentColimitUnitMiddleNativeRelation :
    (functorTriangleSequentialPostComparison (coherentColimitUnitInteriorLast B T) p).app x₀ ≪≫
      (functorTriangleSequentialPostComparison (coherentColimitUnitLowerTriangle B r) p).app
        ((functorHomotopyRelativePost (l) p).app _ x₀) =
    (functorTriangleSequentialPostComparison (coherentColimitUnitInteriorFirst B T) p).app x₀ ≪≫
      VertexIso.map ((functorTriangleSequentialPostComparison (coherentColimitUnitUpperTriangle
        B l) p).app x₀)
        (functorHomotopyRelativePost (simplicialHomotopyOfFunctorEdge
          (coherentColimitConstantEdge B r)) p) :=
  (coherentColimitUnitMiddleBoundary B T).comparison_square

end SerrePositivity.InfinityCategories.F2
