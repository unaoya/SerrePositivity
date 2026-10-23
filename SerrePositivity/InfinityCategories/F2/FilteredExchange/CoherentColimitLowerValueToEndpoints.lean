module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoconeIntervalValueToEndpoints
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitRawIntervalTransport
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitLowerTransportVertices

/-!
概要：raw 区間比較の二端点を、下側輸送因子の実二端点へ固定値の中で戻す。
方針：同じ全区間族の実端点の移送と、既存の native 実頂点式を合成する。
規約：端点は全射から計算する。使われ方：元の下側因子と三角形の値の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)
local notation "c₀" => coherentDiagramTotalCocone F
local notation "z" => JoinCocone.vertex (coherentDiagramTotalCocone G)
local notation "a" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B H)
local notation "a'" => SSet.yonedaEquiv.symm (coherentColimitIntervalVertex B H)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex G)

/-- raw 比較の始点の固定値への像は、下側の元の実合成射の頂点。 -/
lemma coherentColimitLowerRaw_source_valueTo_vertex :
    (coconeIntervalRelativeComposite c₀ a ≫
      (constantUnstraighteningRelativeIso (leftUnstraighteningProjection F) z).hom ≫
        (ihom (leftUnstraightening F)).map V).app (Opposite.op ⦋0⦌) l =
      functorVertex (coherentColimitLowerCompositeAction B H) := by
  exact (coconeIntervalRelativeComposite_valueTo_vertex_eq c₀
    (coherentDiagramTotalCocone_vertex G) a a'
    (coherentColimitRawIntervalFamily_heq_native B H) l).trans
    (coherentColimitLowerFactor_middle_vertex B H)

/-- raw 普遍輸送の終点の固定値への像は、下側因子の同じ実 fiber 輸送の頂点。 -/
lemma coherentColimitLowerRaw_target_valueTo_vertex :
    ((pointedIntervalTransport a).map ≫
      (pre (coconeFiberMap c₀)).app (vertexFiber pointedSpaceProjection z) ≫
        (ihom (leftUnstraightening F)).map V).app (Opposite.op ⦋0⦌) l =
      functorVertex (coconeFiberMap c₀ ≫ coherentColimitFiberTransport B H ≫
        (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G)).hom) := by
  exact (coconeIntervalTransport_valueTo_vertex_eq c₀ (coherentDiagramTotalCocone_vertex G)
    a a' (coherentColimitRawIntervalFamily_heq_native B H) l).trans
    (coherentColimitLowerFactor_target_vertex B H)

end SerrePositivity.InfinityCategories.F2
