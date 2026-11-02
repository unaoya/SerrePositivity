module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexRawLongCanonical
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedMorphismEdgeValueRatioFactory
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedMorphismUniversalActionPrecomp

/-!
概要：元の実長辺の raw 値比較の逆と指定普遍比較を、元の同じ右評価比較へ戻す。
方針：同じ実長辺と元の全初期係数を generic な実辺の二因子消去へ代入する。
規約：元の全係数・指定値を保持。使われ方：長辺評価比較の式の最後の因子。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
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
local notation "C" => pointedCoherentFiberComparison K₀ ≫
  eqToHom (congrArg (vertexFiber pointedSpaceProjection)
    (Eq.symm (spaceInfinityVertex_eq_coherent K₀)))

/-- 元の長辺の raw 値比較の逆と同じ指定普遍比較の値の合成。 -/
def coherentColimitApexLongRawValueRatio :=
  (pointedMorphismEdgeValueRatio f (coherentColimitRawSpaceEdge B d)
    h₀ (coherentColimitApex_raw_two_vertex B T)
    ((coherentColimitRawSpaceEdge_long B a T).trans
      (pointedRightMorphismEdge_recover (SpaceInfinity.δ 1 s)).symm)).precomp q

/-- 元の同じ二因子は、元の同じ右作用比較の標準全初期係数による前合成の値。 -/
lemma coherentColimitApexLongRawValueRatio_heq_standard :
    HEq (coherentColimitApexLongRawValueRatio B T)
      ((pointedValueMorphismUniversalActionIso f).precomp C) := by
  have h := pointedMorphismEdgeValueRatio_precomp_heq_action
    («C» := spaceSimplexPointedCoefficients s) f (coherentColimitRawSpaceEdge B d)
    h₀ (coherentColimitApex_raw_two_vertex B T)
    ((coherentColimitRawSpaceEdge_long B a T).trans
      (pointedRightMorphismEdge_recover (SpaceInfinity.δ 1 s)).symm) q
  exact h.trans (functorIso_precomp_heq_of_map_eq (pointedValueMorphismUniversalActionIso f)
    (coherentColimitApexCoefficientMap_standard B T))

/-- 元の同じ二因子は、元の評価比較に現れる同じ全 Hom 成分の指定値。 -/
lemma coherentColimitApexLongRawValueRatio_heq_evaluation :
    HEq (coherentColimitApexLongRawValueRatio B T)
      (VertexIso.map (pointedValueHomActionAt f)
        ((pre C).app ((SSet.uliftFunctor.{u + 1, u}).obj (KanObject.obj K₂)))) := by
  exact (coherentColimitApexLongRawValueRatio_heq_standard B T).trans
    (pointedValueMorphismUniversalActionIso_precomp_heq_evaluation f C)

/-- 同じ元の raw 長辺値比較を先に合成すると、同じ指定普遍比較の値へ厳密に戻る。 -/
lemma coherentColimitApexLongRawValueRatio_cancel :
    (coherentColimitApexRawLongValueIso B T).precomp q ≪≫
      coherentColimitApexLongRawValueRatio B T =
    ((pointedIntervalTransportAt_universalIso D l).postcomp V₂).precomp q :=
  pointedMorphismEdgeValueRatio_precomp_cancel f (coherentColimitRawSpaceEdge B d)
    h₀ (coherentColimitApex_raw_two_vertex B T)
    ((coherentColimitRawSpaceEdge_long B a T).trans
      (pointedRightMorphismEdge_recover (SpaceInfinity.δ 1 s)).symm) q

end SerrePositivity.InfinityCategories.F2
