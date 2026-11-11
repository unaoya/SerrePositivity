module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTriangleCoefficientRecovery
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportSquareWholeEquality
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportTriangleFromSimplex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.KanRightCompositionTransport

/-!
概要：元の Kan 合成三角形を被覆する実三角形の底は、元の合成四角形そのもの。
方針：同じ全図式の回収式と四角形の境界の一意性を使う。
規約：元の頂点表示・全係数を保持。使われ方：四面体則を元の指定合成比較へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の Kan 合成三角形を被覆する実全図式の底は、元の同時係数合成四角形。 -/
lemma transportTriangleBaseOfLift_eq_coherentKanSquare
    {K L M : KanObject.{u}} {P : SSet.{u + 1}}
    (q : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L) ⊗
      (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom L M))
    (W : (Δ[2] : SSet.{u + 1}) ⊗ P ⟶ PointedSpaceInfinity.{u})
    (f : P ⟶ vertexFiber pointedSpaceProjection (spaceInfinityVertex K))
    (g : P ⟶ vertexFiber pointedSpaceProjection (spaceInfinityVertex L))
    (h : P ⟶ vertexFiber pointedSpaceProjection (spaceInfinityVertex M))
    (h₀ : (prismEndpoint 0 P ≫ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫ W =
      f ≫ vertexFiberι pointedSpaceProjection (spaceInfinityVertex K))
    (h₁ : (prismEndpoint 1 P ≫ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫ W =
      g ≫ vertexFiberι pointedSpaceProjection (spaceInfinityVertex L))
    (h₂ : (prismEndpoint 1 P ≫ (stdSimplex.δ (1 : Fin 3) ▷ P)) ≫ W =
      h ≫ vertexFiberι pointedSpaceProjection (spaceInfinityVertex M))
    (hWp : W ≫ pointedSpaceProjection =
      (Δ[2] ◁ q) ≫ coherentCompositionTriangle K L M) :
    transportTriangleBaseOfLift pointedSpaceProjection W f g h h₀ h₁ h₂ =
      (coherentKanRightCompositionSquare K L M).precomp q := by
  apply transportIntervalSquare_eq_of_square
  change transportTriangleParameter P ≫ (W ≫ pointedSpaceProjection) =
    (Δ[1] ◁ (Δ[1] ◁ q)) ≫ coherentCompositionSquare K L M
  rw [hWp, coherentCompositionSquare_triangle_recovery_precomp]

end SerrePositivity.InfinityCategories.F2
