module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceCompositionZeroFirstPrism
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceCompositionZeroLastPrism
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceTrianglePointedVertexActions
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedVertexBase

/-!
概要：零面・元の全三角形・最大化側の標準族の実中間点を同じ全係数射に揃える。
方針：元の第一辺の全 Hom 作用と同じ実初辺の等式を使う。
規約：全初点係数を保持。使われ方：零面の指定比較の中間像の恒等性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "A" => spaceSimplexPointedCoefficients s
local notation "K₁" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 1))

/-- 元の第一辺による同じ全初点 Hom の実中間 fiber 内への作用。 -/
def spaceCompositionZeroMiddleMap : A ⟶ vertexFiber pointedSpaceProjection
    (coherentNerveVertex K₁) :=
  (SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map
    (eHomWhiskerLeft SSet pointKanObject (coherentEdgeHom (SpaceInfinity.δ 2 s)))) ≫
      pointedCoherentFiberComparison K₁

/-- 元の同じ全三角形の中間点作用は、公開した同じ実中間射の包含。 -/
lemma spaceCompositionZeroMiddleMap_original :
    simplexPrismVertex 2 1 A ≫ spaceSimplexPointedFamily s =
      spaceCompositionZeroMiddleMap s ≫ vertexFiberι pointedSpaceProjection
        (coherentNerveVertex K₁) := by
  simpa only [spaceCompositionZeroMiddleMap, Category.assoc] using
    spaceTrianglePointedFamily_middle_action s

/-- 零面の中間点作用も、同じ実中間射の包含。 -/
lemma spaceCompositionZeroMiddleMap_zero :
    simplexPrismVertex 2 1 A ≫ spaceCompositionTetrahedronZeroFamily s =
      spaceCompositionZeroMiddleMap s ≫ vertexFiberι pointedSpaceProjection
        (coherentNerveVertex K₁) :=
  (spaceCompositionZeroFamily_middle_eq_original s).trans
    (spaceCompositionZeroMiddleMap_original s)

/-- 最大化側の標準族も、同じ実初辺の終点で同じ実中間射に一致する。 -/
lemma spaceCompositionZeroMiddleMap_standard :
    simplexPrismVertex 2 1 A ≫ spaceSimplexPointedFamily (coherentSimplexMaximalization s) =
      spaceCompositionZeroMiddleMap s ≫ vertexFiberι pointedSpaceProjection
        (coherentNerveVertex K₁) := by
  have he : prismEndpoint 1 A ≫ (stdSimplex.δ (2 : Fin 3) ▷ A) =
      simplexPrismVertex 2 1 A := by
    apply SSet.hom_ext
    intro n
    rfl
  have h := congrArg (fun q => prismEndpoint 1 A ≫ q)
    (spaceCompositionZeroFamily_first_eq_standard s).symm
  have hm : simplexPrismVertex 2 1 A ≫
      spaceSimplexPointedFamily (coherentSimplexMaximalization s) =
      simplexPrismVertex 2 1 A ≫ spaceCompositionTetrahedronZeroFamily s := by
    simpa only [← Category.assoc, he] using h
  exact hm.trans (spaceCompositionZeroMiddleMap_zero s)

/-- 最大化側の実中間点の底は、元の同じ coherent 中間対象に定値。 -/
lemma spaceCompositionZeroMiddle_base :
    simplexPrismVertex 2 1 A ≫ (fst Δ[2] A ≫
      SSet.yonedaEquiv.symm (coherentSimplexMaximalization s)) =
        SSet.const (coherentNerveVertex K₁) :=
  spaceSimplexPointedVertex_base (coherentSimplexMaximalization s) 1

end SerrePositivity.InfinityCategories.F2
