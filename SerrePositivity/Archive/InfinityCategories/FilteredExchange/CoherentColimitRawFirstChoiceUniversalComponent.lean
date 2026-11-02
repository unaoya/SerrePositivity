module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawFirstChoiceComponentTransport
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawUniversalTriangleComparison

/-!
概要：全第一辺比較の普遍第一辺成分を、元の同じ普遍三角形の指定比較へ値まで同定する。
方針：元の二実辺を回収し、二辺固定の全長辺比較の一致を使う。
規約：元の二単体と二普遍辺を保持。使われ方：新長辺残余と最初辺輸送比較の交換式。
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
  (f : K ⟶ vertexFiber pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone F)))

/-- 元の普遍第一辺の全比較成分は、元の同じ普遍二辺三角形の指定比較そのもの。 -/
lemma coherentColimitRawFirstChoiceTriangleComparisonApp_universal_heq :
    HEq (coherentColimitRawFirstChoiceTriangleComparisonApp B T f
      (coherentColimitRawFirstChoiceUniversalVertex B a f))
      (coherentColimitRawUniversalTriangleComparison B T f) := by
  have hh := coherentColimitRawFirstChoiceTriangleComparisonApp_heq_transport B T f
    (coherentColimitRawTransportPointPrism B a f)
    (coherentColimitRawTransportPointPrism_projection B a f)
    (coherentColimitRawTransportPointPrism_start B a f)
    (f ≫ coherentColimitRawFiberTransport B a) (coherentColimitRawTransportPointPrism_finish B a f)
    (coherentColimitRawUniversalTrianglePrism B T f)
    (coherentColimitRawUniversalTrianglePrism_projection B T f)
    (coherentColimitRawUniversalTrianglePrism_first B T f)
    (coherentColimitRawUniversalTrianglePrism_last B T f)
    (coherentColimitRawUniversalTriangleLongTransport B T f)
    (coherentColimitRawUniversalTriangleLongTransport_point_prism B T f
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
  exact hh.trans (coherentColimitRawUniversalTriangleComparison_heq_pointed B T f).symm

end SerrePositivity.InfinityCategories.F2
