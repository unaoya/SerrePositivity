module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitApexRawLongCanonical
public import SerrePositivity.InfinityCategories.F2.PointedUniversalEdgeValuePrecomp

/-!
概要：元の実長辺の指定一点普遍比較を、同じ canonical 区間の標準初期係数へ戻す。
方針：元の実辺・両端の表示変更と元の初期係数の標準表示を合わせる。
規約：元の指定比較と全係数を保持。使われ方：元の長辺評価比較の二因子の合成。
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
local notation "K₂" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))
local notation "f" => coherentEdgeHom (SpaceInfinity.δ 1 s)
local notation "D" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B d)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "q" => coherentColimitApexCoefficientMap B T
local notation "h₀" => coherentColimitApex_raw_zero_vertex B T
local notation "V₂" => pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T)
local notation "R" => SSet.yonedaEquiv.symm
  (intervalMappingVertexOfEdge (pointedRightMorphismEdge f))
local notation "V" => QCatEquivalence.hom
  (pointedSpaceFiberValueEquivalence (spaceInfinityVertex K₂))
local notation "C" => pointedCoherentFiberComparison K₀ ≫
  eqToHom (congrArg (vertexFiber pointedSpaceProjection)
    (Eq.symm (spaceInfinityVertex_eq_coherent K₀)))

/-- 元の長辺の普遍比較の値は、同じ canonical 指定値の同じ移送初期係数での値。 -/
lemma coherentColimitApexLongUniversalValue_heq_canonical :
    HEq (((pointedIntervalTransportAt_universalIso D l).precomp q).postcomp V₂)
      (((pointedIntervalTransportAt_universalIso R l).postcomp V).precomp
        (q ≫ eqToHom (congrArg (vertexFiber pointedSpaceProjection) h₀))) :=
  pointedIntervalUniversalIso_edge_value_change_precomp f
    (coherentColimitRawSpaceEdge B d) h₀ (coherentColimitApex_raw_two_vertex B T)
    ((coherentColimitRawSpaceEdge_long B a T).trans
      (pointedRightMorphismEdge_recover (SpaceInfinity.δ 1 s)).symm) q

/-- 同じ元の長辺の普遍比較の値は、元の標準 coherent 初期係数での canonical 指定値。 -/
lemma coherentColimitApexLongUniversalValue_heq_standard :
    HEq (((pointedIntervalTransportAt_universalIso D l).precomp q).postcomp V₂)
      (((pointedIntervalTransportAt_universalIso R l).postcomp V).precomp C) := by
  exact (coherentColimitApexLongUniversalValue_heq_canonical B T).trans
    (functorIso_precomp_heq_of_map_eq
      ((pointedIntervalTransportAt_universalIso R l).postcomp V)
      (coherentColimitApexCoefficientMap_standard B T))

end SerrePositivity.InfinityCategories.F2
