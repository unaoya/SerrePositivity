module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.IteratedLocalNativeGlobalCoherence
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorIsoEndpointPrecomposition

/-!
概要：既存の局所結合比較を元の全 Hom に戻した両端は、導出した同じ第一因子の両端。
方針：元の二因子の端点回収を、同じ端点正規化と前合成の一般則で運ぶ。
規約：元の全 Hom 作用と既存の指定局所結合比較を保持する。
使われ方：指定結合比較と制限自然性を元の全 Hom 上で貼り合わせる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 既存の局所結合比較は、元の二重底変換で前合成しても同じ両端を回収する。 -/
lemma cocartesianIteratedLocalHomComparison_nativeIso_originalHom_endpoints
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    ((cocartesianIteratedLocalHomComparison_nativeIso l k p q).precomp
      (cocartesianDoubleBaseChangeHomAction l k p q)).sourceMap =
      (cocartesianBaseChangeGlobalTransportCompositionIso l k p q).targetMap ∧
    ((cocartesianIteratedLocalHomComparison_nativeIso l k p q).precomp
      (cocartesianDoubleBaseChangeHomAction l k p q)).targetMap =
      (cocartesianBaseChangeGlobalNativeTransportPostIso l k p q).targetMap := by
  have hs := functorIsoOfEq_precomp_sourceMap_of_eq
    (cocartesianIteratedLocalNativeCompositeIso l k p q)
    (cocartesianIteratedLocalNativeComposite_source l k p q)
    (cocartesianIteratedLocalNativeComposite_target l k p q)
    (cocartesianDoubleBaseChangeHomAction l k p q)
    (cocartesianBaseChangeGlobalComposition_native_target l k p q)
  have ht₀ := functorIsoOfEq_precomp_targetMap_recover
    (cocartesianIteratedLocalNativeTransportFactorIso l k p q)
    (cocartesianIteratedLocalNativeTransportFactor_source l k p q)
    (cocartesianDoubleBaseChangeHomAction l k p q)
    (cocartesianBaseChangeGlobalNativeTransport_native_target l k p q)
  have ht := functorIsoOfEq_precomp_targetMap_of_eq
    (cocartesianIteratedLocalNativeCompositeIso l k p q)
    (cocartesianIteratedLocalNativeComposite_source l k p q)
    (cocartesianIteratedLocalNativeComposite_target l k p q)
    (cocartesianDoubleBaseChangeHomAction l k p q)
    ht₀
  exact ⟨hs, ht⟩

end SerrePositivity.InfinityCategories
