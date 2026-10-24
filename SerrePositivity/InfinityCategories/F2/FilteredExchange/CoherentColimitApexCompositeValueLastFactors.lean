module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexLastValueSquare
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexRawCompositeValue
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoTwoEdgeValueReindex
/-!
概要：元の終点比較と raw 二辺値を、実最後辺の値正方形と同じ第一辺値へ分解する。
方針：全係数の二辺値を同じ二因子へ戻し、同じ raw 比だけを消去して戻す。
規約：元の全初期値・二 raw 値・実中間比較を保持する。
使われ方：Ncomp の最大化側の値と元の raw 二辺値の照合。
-/

@[expose] public section
open CategoryTheory SSet
open scoped Simplicial
noncomputable section
namespace SerrePositivity.InfinityCategories.F2
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "s" => coherentColimitApexTriangle B T
local notation "q" => coherentColimitApexCoefficientMap B T
local notation "V₀" => pointedFiberValueTo (coherentColimitApex_raw_zero_vertex B T)
local notation "V₁" => pointedFiberValueTo (coherentColimitApex_raw_one_vertex B T)
local notation "V₂" => pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T)
local notation "uf" => CategoryTheory.Functor.map SSet.uliftFunctor
  (coherentEdgeHom (SpaceInfinity.δ 2 s))
local notation "ug" => CategoryTheory.Functor.map SSet.uliftFunctor
  (coherentEdgeHom (SpaceInfinity.δ 0 s))
local notation "ta" => coherentColimitRawFiberTransport B a
local notation "tb" => coherentColimitRawFiberTransport B b
/-- 概要：元の第一辺値を同じ全初期値と最後射で読む指定値。方針：同じ因子の結合表示を揃える。
規約：元の指定値を保持。使われ方：Ncomp の元の raw 因子の回収。 -/
def coherentColimitApexFirstValueAfterLast :=
  functorIsoEdgeValuePostAt ta V₀ V₁ uf (coherentColimitApexRawFirstValueIso B T) q ug
/-- 概要：元の raw 二辺値の同じ指定最後辺・第一辺の二因子。方針：同じ因子の結合表示を揃える。
規約：元の指定値を保持。使われ方：Ncomp の元の raw 因子の回収。 -/
lemma coherentColimitApexCompositeValueComposite_eq_last_first :
    coherentColimitApexCompositeValueComposite B T =
      coherentColimitApexLastValueComposite B T ≪≫ coherentColimitApexFirstValueAfterLast B T := by
  have h := functorIsoTwoEdgeValue_precomp_eq_factors ta tb V₀ V₁ V₂ uf ug
    (coherentColimitApexRawFirstValueIso B T) (coherentColimitApexRawLastValueIso B T) q
  have hh := congrArg (fun e =>
    (coherentColimitApexPointedTargetEndpointIso B T).postcomp V₂ ≪≫ e) h
  convert hh.trans (Iso.trans_assoc _ _ _).symm using 1 <;> rfl
/-- 概要：元の raw 二辺値を同じ実最後辺の正方形と第一辺値へ分解。方針：同じ因子の結合表示を揃える。
規約：元の指定値を保持。使われ方：Ncomp の元の raw 因子の回収。 -/
lemma coherentColimitApexCompositeValueComposite_eq_last_square_factors :
    coherentColimitApexCompositeValueComposite B T =
      (coherentColimitApexLastDiagonalComparison B T).postcomp V₂ ≪≫
        (coherentColimitApexLastNativeImageIso B T).postcomp V₂ ≪≫
        (coherentColimitApexLastSquareRawValueRatio B T).symm ≪≫
        coherentColimitApexFirstValueAfterLast B T := by
  have h := congrArg (fun e => e ≪≫ (coherentColimitApexLastSquareRawValueRatio B T).symm)
    (coherentColimitApexLastValueComposite_trans_ratio B T)
  simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] at h
  rw [coherentColimitApexCompositeValueComposite_eq_last_first]
  simpa only [Iso.trans_assoc] using congrArg
    (fun e => e ≪≫ coherentColimitApexFirstValueAfterLast B T) h
end SerrePositivity.InfinityCategories.F2
