module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexFirstEndpointSquare
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedMorphismFixedDiagonalComparison
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedReverseDiagonalPrismFixed
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.DiagonalPrismBoundaryValue
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedFiberValueToDisplay
/-!
概要：元の第一面の指定対角値を同じ第一射の元の全 Hom 値比較へ戻す。
方針：同じ実 prism・実両端と値射を固定射の指定対角比較に照合する。
規約：元の全初期係数・第一射・指定値を保持する。
使われ方：元の中間比較と第一 raw 辺値から評価比較への帰還。
-/

@[expose] public section
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "s" => coherentColimitApexTriangle B T
local notation "f" => coherentEdgeHom (SpaceInfinity.δ 2 s)
local notation "V₁" => pointedFiberValueTo (coherentColimitApex_raw_one_vertex B T)
/-- 概要：同じ元の第一指定対角比較の値は元の第一射の同じ値比較。
方針：同じ実 prism と fiber 頂点・値射で指定対角比較を照合する。
規約：全係数と指定値を保持。使われ方：第一辺評価の因子式。 -/
lemma coherentColimitApexFirstDiagonal_post_value_heq_morphism :
    HEq ((coherentColimitApexFirstDiagonalComparison B T).postcomp V₁)
      (pointedHomMorphismValueComparison f) := by
  refine HEq.trans ?_ (pointedHomMorphismValueComparison_heq_fixed_diagonal f).symm
  unfold pointedMorphismFixedDiagonalComparison
  apply diagonalTransportIso_postcomp_heq_of_boundary
  · exact coherentColimitApex_raw_zero_vertex B T
  · exact coherentColimitApex_raw_one_vertex B T
  · exact (eq_of_heq (coherentColimitApexPointedFirstPrism_heq_morphism B T)).trans
      (pointedReverseDiagonalPrism_fixed_eq_coherent f).symm
  · exact pointedFiberValueTo_heq_value (coherentColimitApex_raw_one_vertex B T)
end
end SerrePositivity.InfinityCategories.F2
