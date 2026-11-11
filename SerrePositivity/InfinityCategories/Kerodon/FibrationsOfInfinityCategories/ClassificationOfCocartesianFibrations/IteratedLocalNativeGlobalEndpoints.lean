module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IteratedLocalNativeGlobalCoherence
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoEndpointPrecomposition

/-!
概要：既存の局所結合比較を元の全 Hom に戻した両端は、導出した同じ第一因子の両端。
方針：元の二因子の端点回収を、同じ端点正規化と前合成の一般則で運ぶ。
規約：元の全 Hom 作用と既存の指定局所結合比較を保持する。
使われ方：指定結合比較と制限自然性を元の全 Hom 上で貼り合わせる。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 既存の局所結合比較は、元の二重底変換で前合成しても同じ両端を回収する。 -/
lemma cocartesianIteratedLocalHomComparison_nativeIso_originalHom_endpoints
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C)) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIteratedLocalHomComparison_nativeIso l k p q).precomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianDoubleBaseChangeHomAction l k p q)).sourceMap =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeGlobalTransportCompositionIso l k p q).targetMap ∧
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIteratedLocalHomComparison_nativeIso l k p q).precomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianDoubleBaseChangeHomAction l k p q)).targetMap =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeGlobalNativeTransportPostIso l k p q).targetMap := by
  have hs := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_precomp_sourceMap_of_eq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIteratedLocalNativeCompositeIso l k p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIteratedLocalNativeComposite_source l k p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIteratedLocalNativeComposite_target l k p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianDoubleBaseChangeHomAction l k p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeGlobalComposition_native_target l k p q)
  have ht₀ := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_precomp_targetMap_recover
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIteratedLocalNativeTransportFactorIso l k p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIteratedLocalNativeTransportFactor_source l k p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianDoubleBaseChangeHomAction l k p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeGlobalNativeTransport_native_target l k p q)
  have ht := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_precomp_targetMap_of_eq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIteratedLocalNativeCompositeIso l k p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIteratedLocalNativeComposite_source l k p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIteratedLocalNativeComposite_target l k p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianDoubleBaseChangeHomAction l k p q)
    ht₀
  exact ⟨hs, ht⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
