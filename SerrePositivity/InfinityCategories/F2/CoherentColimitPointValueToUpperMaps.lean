module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitConstantPointValueToUpper

/-!
概要：一点比較の raw 上面による前合成の実両端を、最後辺の下側因子の前合成へ揃える。
方針：同じ元の単位の実端点式を、元の最初辺の実作用で前合成する。
規約：全射から端点を計算。使われ方：指定自然性の四角形の実頂点正規化。
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
local notation "z₁" => JoinCocone.vertex (coherentDiagramTotalCocone G)
local notation "z₃" => JoinCocone.vertex (coherentDiagramTotalCocone J)
local notation "f" => Subtype.val (leftUnstraighteningMappingVertexMap F G
  (coherentVertexOfHomotopy a))
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex J)
local notation "g₀" => Subtype.val (leftUnstraighteningMappingVertexMap
  (SSet.const z₁) (SSet.const z₃) (coherentVertexOfHomotopy
    (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B b)))) ≫
      constantUnstraighteningFiberProjection (CategoryTheory.Functor.obj SSet.uliftFunctor B) z₃ ≫ V
local notation "P" => constantUnstraighteningFiberProjection
  (CategoryTheory.Functor.obj SSet.uliftFunctor B) z₁
local notation "A" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B b)
local notation "s" => lift (𝟙 _) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
local notation "g₁" => (s ≫ (P ▷ Δ[0]) ≫
  FiberTransportFamily.endpoint (pointedIntervalTransport A)) ≫ V

/-- 同じ上面上の一点比較の実始点は、最後辺の下側実合成射の元の前合成。 -/
lemma coherentColimitPointValueTo_upper_source_map :
    coherentColimitRawUpperCompositeAction B a ≫ g₀ =
      f ≫ coherentColimitLowerCompositeAction B b := by
  have h := functorVertex_injective (coherentColimitLowerPoint_source_valueTo_vertex B b)
  have hh := congrArg (fun k => f ≫ k) h
  simpa only [coherentColimitRawUpperCompositeAction, coherentVertexOfHomotopy_cocone,
    Category.assoc] using hh

/-- 同じ上面上の一点比較の実終点は、最後辺の同じ fiber 輸送の元の前合成。 -/
lemma coherentColimitPointValueTo_upper_target_map :
    coherentColimitRawUpperCompositeAction B a ≫ g₁ =
      f ≫ (coconeFiberMap (coherentDiagramTotalCocone G) ≫ coherentColimitFiberTransport B b ≫
        (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex J)).hom) := by
  have h := functorVertex_injective (coherentColimitLowerPoint_target_valueTo_vertex B b)
  have hh := congrArg (fun k => f ≫ k) h
  simpa only [coherentColimitRawUpperCompositeAction, coherentVertexOfHomotopy_cocone,
    Category.assoc] using hh

/-- 上面上の元の一点比較を実両端で揃えると、最後辺の下側因子の元の前合成に等しい。 -/
lemma coherentColimitPointValueTo_upper_eq_lower :
    functorIsoOfEq ((coherentColimitConstantPointValueToIso B b).precomp
      (coherentColimitRawUpperCompositeAction B a))
      (coherentColimitPointValueTo_upper_source_map B a b)
      (coherentColimitPointValueTo_upper_target_map B a b) =
    (coherentColimitLowerTransportFactorIso B b).precomp f := by
  exact eq_of_heq ((functorIsoOfEq_heq _ _ _).trans
    (coherentColimitConstantPointValueTo_upper_heq_lower B a b))

end SerrePositivity.InfinityCategories.F2
