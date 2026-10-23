module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexVertexCoefficientMaps
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedFiberCoherentValueCast

/-!
概要：元の余極限三角形の三つの全係数の値を、同じ coherent fiber の値へ戻す。
方針：元の実頂点の等式と指定された値射の移送を合成する。
規約：元の実 fiber・全係数・三辺を保持。使われ方：長辺値式への全作用の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "s" => coherentColimitApexTriangle B T
local notation "K₀" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "K₁" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 1))
local notation "K₂" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))

/-- 元の初点の全係数の値は、同じ coherent 比較を標準初点値で読んだ射。 -/
lemma coherentColimitApexCoefficientMap_value :
    coherentColimitApexCoefficientMap B T ≫
      pointedFiberValueTo (coherentColimitApex_raw_zero_vertex B T) =
    pointedCoherentFiberComparison K₀ ≫
      eqToHom (congrArg (vertexFiber pointedSpaceProjection)
        (spaceInfinityVertex_eq_coherent K₀).symm) ≫
      (pointedSpaceFiberValueEquivalence (spaceInfinityVertex K₀)).hom := by
  simp only [coherentColimitApexCoefficientMap, Category.assoc]
  rw [pointedFiberValueTo_coherent_cast]

/-- 元の中間係数の値は、元の第一辺の全作用を標準中間値で読んだ射。 -/
lemma coherentColimitApexMiddleCoefficientMap_value :
    coherentColimitApexMiddleCoefficientMap B T ≫
      pointedFiberValueTo (coherentColimitApex_raw_one_vertex B T) =
    (SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map
      (eHomWhiskerLeft SSet pointKanObject (coherentEdgeHom (SpaceInfinity.δ 2 s)))) ≫
      pointedCoherentFiberComparison K₁ ≫
      eqToHom (congrArg (vertexFiber pointedSpaceProjection)
        (spaceInfinityVertex_eq_coherent K₁).symm) ≫
      (pointedSpaceFiberValueEquivalence (spaceInfinityVertex K₁)).hom := by
  simp only [coherentColimitApexMiddleCoefficientMap, Category.assoc]
  rw [pointedFiberValueTo_coherent_cast]

/-- 元の終点係数の値は、元の長辺の全作用を標準終点値で読んだ射。 -/
lemma coherentColimitApexTargetCoefficientMap_value :
    coherentColimitApexTargetCoefficientMap B T ≫
      pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T) =
    (SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map
      (eHomWhiskerLeft SSet pointKanObject (coherentEdgeHom (SpaceInfinity.δ 1 s)))) ≫
      pointedCoherentFiberComparison K₂ ≫
      eqToHom (congrArg (vertexFiber pointedSpaceProjection)
        (spaceInfinityVertex_eq_coherent K₂).symm) ≫
      (pointedSpaceFiberValueEquivalence (spaceInfinityVertex K₂)).hom := by
  simp only [coherentColimitApexTargetCoefficientMap, Category.assoc]
  rw [pointedFiberValueTo_coherent_cast]

end SerrePositivity.InfinityCategories.F2
