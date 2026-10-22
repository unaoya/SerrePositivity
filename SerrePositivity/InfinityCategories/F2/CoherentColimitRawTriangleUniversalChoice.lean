module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitRawFirstChoicePointIndependence
public import SerrePositivity.InfinityCategories.F2.CoherentColimitRawTrianglePointTransport
public import SerrePositivity.InfinityCategories.F2.CoherentColimitRawUniversalTriangleComparison

/-!
概要：元の二つの普遍辺を持つ任意の全三角形から、元の指定普遍比較を回収する。
方針：二辺固定の長辺比較の一意性と、元の全輸送の指定一点成分を使う。
規約：元の全図式と二実辺を保持。使われ方：係数制限による比較の忠実な反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d) {K : SSet.{u + 1}}
  (f : K ⟶ vertexFiber pointedSpaceProjection (coherentDiagramTotalCocone F).vertex)
local notation "W" => coherentColimitRawTransportPointPrism B a f
local notation "hs" => coherentColimitRawTransportPointPrism_start B a f
local notation "hp" => coherentColimitRawTransportPointPrism_projection B a f
local notation "g" => f ≫ coherentColimitRawFiberTransport B a
local notation "hg" => coherentColimitRawTransportPointPrism_finish B a f
local notation "X" => coherentColimitRawUniversalTrianglePrism B T f

/-- 元の二つの普遍辺を持つ任意の全持ち上げから、同じ指定普遍比較を値まで回収する。 -/
lemma coherentColimitRawTriangleLongPointComparison_eq_universal
    (Y : (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ PointedSpaceInfinity.{u})
    (hY : Y ≫ pointedSpaceProjection =
      fst Δ[2] K ≫ T.diagram ≫ coherentColimitFunctor B)
    (hfirst : (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ Y = W)
    (hlast : (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ Y =
      coherentColimitRawTransportPointPrism B b g) :
    coherentColimitRawTriangleLongPointComparison B T f W hs g Y hY hfirst hlast =
      coherentColimitRawUniversalTriangleComparison B T f := by
  have hy := coherentColimitRawFirstChoiceTrianglePointComparison_eq_of_fixed_edges
    B T f W hp hs g hg Y hY hfirst hlast
  have hx := coherentColimitRawFirstChoiceTrianglePointComparison_eq_of_fixed_edges
    B T f W hp hs g hg X (coherentColimitRawUniversalTrianglePrism_projection B T f)
    (coherentColimitRawUniversalTrianglePrism_first B T f)
    (coherentColimitRawUniversalTrianglePrism_last B T f)
  have ht := coherentColimitRawTriangleLongPointComparison_heq_transport B T f W hs g X
    (coherentColimitRawUniversalTrianglePrism_projection B T f)
    (coherentColimitRawUniversalTrianglePrism_first B T f)
    (coherentColimitRawUniversalTrianglePrism_last B T f)
    (coherentColimitRawUniversalTriangleLongTransport B T f)
    (coherentColimitRawUniversalTriangleLongTransport_point_prism B T f
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
  exact hy.symm.trans (hx.trans (eq_of_heq
    (ht.trans (coherentColimitRawUniversalTriangleComparison_heq_pointed B T f).symm)))

end SerrePositivity.InfinityCategories.F2
