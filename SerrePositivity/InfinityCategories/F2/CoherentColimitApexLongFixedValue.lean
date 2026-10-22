module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitApexLongNativeValue
public import SerrePositivity.InfinityCategories.F2.PointedMorphismFixedDiagonalComparison
public import SerrePositivity.InfinityCategories.F2.CoherentColimitApexLongMorphismPrism
public import SerrePositivity.InfinityCategories.F2.PointedReverseDiagonalPrismFixed
public import SerrePositivity.InfinityCategories.F2.DiagonalPrismBoundaryValue
public import SerrePositivity.InfinityCategories.F2.PointedFiberValueToDisplay

/-!
概要：元の長辺直接比較の値を、同じ元の固定 Kan 射の全値比較へ一致させる。
方針：両指定対角比較の同じ実 prism と両 fiber 頂点・値射を照合する。
規約：元の全初期値・指定値を保持。使われ方：元の長辺評価比較の因子式への代入。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "s" => coherentColimitApexTriangle B T
local notation "f" => coherentEdgeHom (SpaceInfinity.δ 1 s)
local notation "V₂" => pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T)

/-- 元の全実長辺の直接比較の値は、元の同じ固定射の全値比較と値まで一致する。 -/
lemma coherentColimitApexPointedLongNativeComparison_post_value_heq_morphism :
    HEq ((coherentColimitApexPointedLongNativeComparison B T).postcomp V₂)
      (pointedHomMorphismValueComparison f) := by
  refine (coherentColimitApexPointedLongNativeComparison_post_value_heq_diagonal B T).trans ?_
  refine HEq.trans ?_ (pointedHomMorphismValueComparison_heq_fixed_diagonal f).symm
  unfold pointedMorphismFixedDiagonalComparison
  apply diagonalTransportIso_postcomp_heq_of_boundary
  · exact coherentColimitApex_raw_zero_vertex B T
  · exact coherentColimitApex_raw_two_vertex B T
  · exact (eq_of_heq (coherentColimitApexPointedLongPrism_heq_morphism B T)).trans
      (pointedReverseDiagonalPrism_fixed_eq_coherent f).symm
  · exact pointedFiberValueTo_heq_value (coherentColimitApex_raw_two_vertex B T)

end SerrePositivity.InfinityCategories.F2
