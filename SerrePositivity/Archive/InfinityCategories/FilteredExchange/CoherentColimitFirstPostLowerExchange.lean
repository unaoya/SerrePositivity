module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitLastValueToNativeEndpoints
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitFirstPostTransportExchange

/-!
概要：元の最初辺後合成と、最後辺の下側輸送因子の同じ指定自然性を厳密に示す。
方針：元の自然性四角形の四実頂点を、全射から求めた端点等式で揃える。
規約：元の四因子を保持。使われ方：模型五因子式の上側単位の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  (a : SSet.Homotopy F G) (b : SSet.Homotopy G J)
local notation "p" => leftUnstraighteningProjection F
local notation "x₀" => relativeFunctorVertex p p (𝟙 (leftUnstraightening F)) (Category.id_comp p)
local notation "rc" => simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B b)
local notation "Q" => constantTargetValueProjectionTo p (coherentDiagramTotalCocone_vertex J)
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex J)
local notation "f" => Subtype.val (leftUnstraighteningMappingVertexMap F G
  (coherentVertexOfHomotopy a))
local notation "P" => constantUnstraighteningFiberProjection
  (CategoryTheory.Functor.obj SSet.uliftFunctor B)
  (JoinCocone.vertex (coherentDiagramTotalCocone G))
local notation "A" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B b)
local notation "s" => lift (𝟙 _) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
local notation "g₁" => (s ≫ (P ▷ Δ[0]) ≫
  FiberTransportFamily.endpoint (pointedIntervalTransport A)) ≫ V
local notation "g₀" => Subtype.val (leftUnstraighteningMappingVertexMap
  (SSet.const (JoinCocone.vertex (coherentDiagramTotalCocone G)))
  (SSet.const (JoinCocone.vertex (coherentDiagramTotalCocone J)))
  (coherentVertexOfHomotopy rc)) ≫ constantUnstraighteningFiberProjection
    (CategoryTheory.Functor.obj SSet.uliftFunctor B)
    (JoinCocone.vertex (coherentDiagramTotalCocone J)) ≫ V

/-- 元の最初因子を同じ実始点と最後辺の native 始点へ揃えた指定比較。 -/
def coherentColimitFirstPostNativeValueToComparison :
    FunctorIso (coherentColimitRawLowerCompositeAction B a ≫ g₀)
      (f ≫ coherentColimitLowerCompositeAction B b) :=
  vertexIsoOfEq (VertexIso.map (VertexIso.map (coherentColimitUnitValueComparison B a p x₀)
    (functorHomotopyRelativePost rc p)) Q)
    (coherentColimitFirstPost_valueTo_source_vertex B a b)
    (coherentColimitLastValueTo_source_vertex B a b)

/-- 元の最初因子と最後辺の下側因子の交換式は、実四頂点で値まで成立する。 -/
lemma coherentColimitFirstPost_lower_exchange [Quasicategory B] :
    coherentColimitFirstPostNativeValueToComparison B a b ≪≫
      (coherentColimitLowerTransportFactorIso B b).precomp f =
    (coherentColimitConstantPointValueToIso B b).precomp
      (coherentColimitRawLowerCompositeAction B a) ≪≫
    functorIsoOfEq ((coherentColimitRawUnitActionComparison B a).postcomp g₁)
      rfl (coherentColimitPointValueTo_upper_target_map B a b) := by
  have he := (vertexIsoOfEq_heq
    (VertexIso.map (VertexIso.map (coherentColimitUnitValueComparison B a p x₀)
      (functorHomotopyRelativePost rc p)) Q)
    (coherentColimitFirstPost_valueTo_source_vertex B a b)
    (coherentColimitLastValueTo_source_vertex B a b)).trans
    (coherentColimitFirstEdgePost_valueTo_heq_raw B a b)
  exact vertexIso_square_of_heq
    ((coherentColimitRawUnitActionComparison B a).postcomp g₀)
    ((coherentColimitConstantPointValueToIso B b).precomp
      (coherentColimitRawUpperCompositeAction B a))
    ((coherentColimitConstantPointValueToIso B b).precomp
      (coherentColimitRawLowerCompositeAction B a))
    ((coherentColimitRawUnitActionComparison B a).postcomp g₁) _ _ _ _ rfl
    (congrArg functorVertex (coherentColimitPointValueTo_upper_source_map B a b)) rfl
    (congrArg functorVertex (coherentColimitPointValueTo_upper_target_map B a b))
    he.symm (coherentColimitConstantPointValueTo_upper_heq_lower B a b) HEq.rfl
    (functorIsoOfEq_heq _ _ _).symm (coherentColimitFirstPost_pointValueTo_exchange B a b)

end SerrePositivity.InfinityCategories.F2
