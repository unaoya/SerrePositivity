module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawUnitActionComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitConstantTransportPointIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoWhiskerExchange

/-!
概要：元の定値一点輸送比較を固定値へ写し、最初辺の元の二面比較との交換式を示す。
方針：元の一点比較の始点の結合だけを揃え、指定関手同型の前後合成の交換を使う。
規約：両指定比較を保持。使われ方：最初辺の後合成と最後辺の下側因子の接続。
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
local notation "A" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B b)
local notation "P" => constantUnstraighteningFiberProjection
  (CategoryTheory.Functor.obj SSet.uliftFunctor B) z₁
local notation "s" => lift (𝟙 _) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex J)
local notation "fb" => Subtype.val (leftUnstraighteningMappingVertexMap
  (SSet.const z₁) (SSet.const z₃) (coherentVertexOfHomotopy
    (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B b))))
local notation "g₀" => fb ≫ constantUnstraighteningFiberProjection
  (CategoryTheory.Functor.obj SSet.uliftFunctor B) z₃ ≫ V
local notation "g₁" => (s ≫ (P ▷ Δ[0]) ≫
  FiberTransportFamily.endpoint (pointedIntervalTransport A)) ≫ V

omit a in
/-- 元の定値一点比較の固定値への像。始点の結合だけを実後合成の形へ揃える。 -/
def coherentColimitConstantPointValueToIso : FunctorIso g₀ g₁ :=
  functorIsoOfEq ((coherentColimitConstantTransportPointIso B b).postcomp V)
    (Category.assoc _ _ _) rfl

/-- 最初辺の元の二面比較と元の最後辺の一点輸送比較は、同じ指定値の交換式を満たす。 -/
lemma coherentColimitFirstPost_pointValueTo_exchange [Quasicategory B] :
    (coherentColimitRawUnitActionComparison B a).postcomp g₀ ≪≫
      (coherentColimitConstantPointValueToIso B b).precomp
        (coherentColimitRawUpperCompositeAction B a) =
    (coherentColimitConstantPointValueToIso B b).precomp
      (coherentColimitRawLowerCompositeAction B a) ≪≫
        (coherentColimitRawUnitActionComparison B a).postcomp g₁ :=
  functorIso_whisker_exchange (coherentColimitRawUnitActionComparison B a)
    (coherentColimitConstantPointValueToIso B b)

end SerrePositivity.InfinityCategories.F2
