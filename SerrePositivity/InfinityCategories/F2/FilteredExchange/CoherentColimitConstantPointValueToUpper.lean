module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitConstantPointValueTo
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitLowerPointValueToEndpoints
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoUnitPrecompositionTransport

/-!
概要：一点輸送比較の raw 上面での前合成を、最後辺の下側因子の元の前合成へ戻す。
方針：元の単位の実両端を全射から同定し、二段の前合成の結合を使う。
規約：二辺・一点比較・下側因子を保持。使われ方：最初因子の自然性と上側単位消去。
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
local notation "c₁" => coherentDiagramTotalCocone G
local notation "z₃" => JoinCocone.vertex (coherentDiagramTotalCocone J)
local notation "u₁" => Subtype.val (leftUnstraighteningMappingVertexMap G
  (SSet.const (JoinCocone.vertex c₁)) (coherentVertexOfHomotopy (coconeTransformationHomotopy c₁)))
local notation "f" => Subtype.val (leftUnstraighteningMappingVertexMap F G
  (coherentVertexOfHomotopy a))
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex J)
local notation "e" => coherentColimitConstantTransportPointIso B b
local notation "fb" => Subtype.val (leftUnstraighteningMappingVertexMap
  (SSet.const (JoinCocone.vertex c₁)) (SSet.const z₃) (coherentVertexOfHomotopy
    (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B b))))
local notation "P₃" => constantUnstraighteningFiberProjection
  (CategoryTheory.Functor.obj SSet.uliftFunctor B) z₃
local notation "A" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B b)
local notation "s" => lift (𝟙 _) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
local notation "P₁" => constantUnstraighteningFiberProjection
  (CategoryTheory.Functor.obj SSet.uliftFunctor B) (JoinCocone.vertex c₁)

/-- 同じ一点比較の上面作用による前合成は、最後辺の下側因子の最初辺による前合成。 -/
lemma coherentColimitConstantPointValueTo_upper_heq_lower :
    HEq ((coherentColimitConstantPointValueToIso B b).precomp
      (coherentColimitRawUpperCompositeAction B a))
      ((coherentColimitLowerTransportFactorIso B b).precomp f) := by
  have hf : (u₁ ≫ fb ≫ P₃) ≫ V = coherentColimitLowerCompositeAction B b := by
    apply functorVertex_injective
    simpa only [coherentVertexOfHomotopy_cocone] using
      (coherentColimitLowerPoint_source_valueTo_vertex B b)
  have hg : (u₁ ≫ s ≫ (P₁ ▷ Δ[0]) ≫ (pointedIntervalTransport A).endpoint) ≫ V =
      coconeFiberMap c₁ ≫ coherentColimitFiberTransport B b ≫
        (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex J)).hom := by
    apply functorVertex_injective
    simpa only [coherentVertexOfHomotopy_cocone] using
      (coherentColimitLowerPoint_target_valueTo_vertex B b)
  exact functorIso_unit_precomp_transport_heq e V u₁ f (Category.assoc fb P₃ V) rfl
    (coherentColimitLowerTransportFactorIso B b) hf hg
    (coherentColimitLowerTransportFactorIso_heq_constant_point_unit_valueTo B b)

end SerrePositivity.InfinityCategories.F2
