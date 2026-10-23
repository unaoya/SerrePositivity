module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeNativeHomTransportIso
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorIsoEndpointProjection

/-!
概要：元の全局所 Hom の輸送比較は、同じ指定 span の因子比較そのもの。
方針：元の二段の端点正規化を保ち、任意の作用による前合成後も同じ値を回収する。
規約：既存の全局所輸送・指定切断・結合同型を保持する。
使われ方：元の大域 Hom 上で第二面の指定結合因子を照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 元の全局所輸送比較は、同じ因子比較の端点正規化である。 -/
lemma cocartesianIsoTransportNativeHomTransportIso_factor_heq :
    HEq (cocartesianIsoTransportNativeHomTransportIso l k p q)
      (cocartesianIsoTransportNativeHomFactorIso l k p q) := by
  exact F2.functorIsoOfEq_heq (cocartesianIsoTransportNativeHomFactorIso l k p q)
    (congrArg (fun f ↦ f ≫ cocartesianBaseChangeAssociativityHomTransport l k p q)
      (cocartesianIsoTransportNativeHomComparison_one l k p q))
    (cocartesianIsoTransportNativeHomComparison_zero l k p q)

/-- 同じ raw 共役の輸送比較を前合成しても、元の因子比較の値を保つ。 -/
lemma cocartesianIsoTransportNativeHomTransportIso_precomp_factor_heq
    {K : SSet.{u + 1}} (r : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p))
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)))) :
    HEq ((cocartesianIsoTransportNativeHomTransportIso l k p q).precomp r)
      ((cocartesianIsoTransportNativeHomFactorIso l k p q).precomp r) := by
  exact functorIsoOfEq_precomp_heq (cocartesianIsoTransportNativeHomFactorIso l k p q)
    (congrArg (fun f ↦ f ≫ cocartesianBaseChangeAssociativityHomTransport l k p q)
      (cocartesianIsoTransportNativeHomComparison_one l k p q))
    (cocartesianIsoTransportNativeHomComparison_zero l k p q) r

/-- 同じ指定 core 共役の既存輸送も、前合成後に元の因子比較そのものとなる。 -/
lemma cocartesianBaseChangeNativeHomTransportIso_precomp_factor_heq
    {K : SSet.{u + 1}} (r : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p))
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)))) :
    HEq ((cocartesianBaseChangeNativeHomTransportIso l k p q).precomp r)
      ((cocartesianIsoTransportNativeHomFactorIso l k p q).precomp r) := by
  exact (functorIsoOfEq_precomp_heq (cocartesianIsoTransportNativeHomTransportIso l k p q)
    (by rw [cocartesianIsoTransportNativeHomMap_eq]) rfl r).trans
      (cocartesianIsoTransportNativeHomTransportIso_precomp_factor_heq l k p q r)

end SerrePositivity.InfinityCategories
