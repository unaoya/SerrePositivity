module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitRawUnitFiberReflection
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitIntervalModelUnitComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.IsoSandwichInjectivity

/-!
概要：最初辺の元の raw fiber 比較を、a6 の元の模型単位比較の指定値へ結び付ける。
方針：同じ native 中央比較への射影と、元の両外側因子の指定共役式を使う。
規約：模型比較・二面比較を保持。使われ方：輸送後の比較の反映を元の模型値へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (a : SSet.Homotopy F G)
local notation "P" => coherentColimitRawConstantFiberProjection B G
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex G)

/-- 同じ raw fiber 比較の固定値への像と元の外側因子は、元の a6 模型単位比較に等しい。 -/
lemma coherentColimitRawUnitFiber_model_image :
    (coherentColimitLowerTransportFactorIso B a).symm ≪≫
      functorIsoOfEq ((coherentColimitRawUnitFiberComparison B a).postcomp V)
        (coherentColimitRawUnitFiberValue_source_map B a)
        (coherentColimitRawUnitFiberValue_target_map B a) ≪≫
      coherentColimitUpperUnitFactorIso B a =
    coherentColimitIntervalModelUnitComparison B a := by
  rw [coherentColimitRawUnitFiberValue_eq_native]
  exact (coherentColimitIntervalModelUnitComparison_eq_reduced B a).symm

/-- 元の模型単位比較への同じ指定像は、元の raw fiber 二面比較そのものを一意に定める。 -/
lemma coherentColimitRawUnitFiberComparison_eq_iff_model
    (e : FunctorIso (coherentColimitRawLowerCompositeAction B a ≫ P)
      (coherentColimitRawUpperCompositeAction B a ≫ P)) :
    (coherentColimitLowerTransportFactorIso B a).symm ≪≫
      functorIsoOfEq (e.postcomp V)
        (coherentColimitRawUnitFiberValue_source_map B a)
        (coherentColimitRawUnitFiberValue_target_map B a) ≪≫
      coherentColimitUpperUnitFactorIso B a =
      coherentColimitIntervalModelUnitComparison B a ↔
    e = coherentColimitRawUnitFiberComparison B a := by
  constructor
  · intro h
    apply (coherentColimitRawUnitFiberComparison_eq_iff_valueTo B a e).mp
    exact iso_sandwich_injective (coherentColimitLowerTransportFactorIso B a).symm
      (coherentColimitUpperUnitFactorIso B a)
      (h.trans (coherentColimitIntervalModelUnitComparison_eq_reduced B a))
  · intro h
    subst e
    exact coherentColimitRawUnitFiber_model_image B a

end SerrePositivity.InfinityCategories.F2
