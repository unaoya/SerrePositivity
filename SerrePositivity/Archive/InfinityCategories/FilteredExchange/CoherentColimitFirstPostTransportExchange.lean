module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitFirstPostValueToEndpoints
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitConstantPointValueTo

/-!
概要：五因子式の元の最初辺因子を、元の一点輸送比較の同じ自然性四角形へ代入する。
方針：実両端を保つ指定値の等式で一因子だけを置き換える。
規約：元の全式の因子と元の一点比較を保持。使われ方：最後辺の下側因子との消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u}) [Quasicategory B]
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  (a : SSet.Homotopy F G) (b : SSet.Homotopy G J)
local notation "p" => leftUnstraighteningProjection F
local notation "x₀" => relativeFunctorVertex p p (𝟙 (leftUnstraightening F)) (Category.id_comp p)
local notation "rc" => simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B b)
local notation "Q" => constantTargetValueProjectionTo p (coherentDiagramTotalCocone_vertex J)
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex J)
local notation "A" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B b)
local notation "P" => constantUnstraighteningFiberProjection
  (CategoryTheory.Functor.obj SSet.uliftFunctor B)
  (JoinCocone.vertex (coherentDiagramTotalCocone G))
local notation "s" => lift (𝟙 _) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
local notation "g₁" => (s ≫ (P ▷ Δ[0]) ≫
  FiberTransportFamily.endpoint (pointedIntervalTransport A)) ≫ V

/-- 元の最初辺因子と元の一点輸送比較の前合成は、指定自然性の四角形を厳密に満たす。 -/
lemma coherentColimitFirstPost_valueTo_transport_exchange :
    vertexIsoOfEq
      (VertexIso.map (VertexIso.map (coherentColimitUnitValueComparison B a p x₀)
        (functorHomotopyRelativePost rc p)) Q)
      (coherentColimitFirstPost_valueTo_source_vertex B a b)
      (coherentColimitFirstPost_valueTo_target_vertex B a b) ≪≫
      (coherentColimitConstantPointValueToIso B b).precomp
        (coherentColimitRawUpperCompositeAction B a) =
    (coherentColimitConstantPointValueToIso B b).precomp
      (coherentColimitRawLowerCompositeAction B a) ≪≫
        (coherentColimitRawUnitActionComparison B a).postcomp g₁ := by
  rw [coherentColimitFirstPost_valueTo_eq_raw]
  exact coherentColimitFirstPost_pointValueTo_exchange B a b

end SerrePositivity.InfinityCategories.F2
