module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleAugmentationRawFactor
/-!
概要：元の augmentation の resolved 比較と、同じ raw factor 比較の正方形が可換。
方針：元の raw factor の入力自然性を書き換え、指定前合成比較とその逆を相殺する。
規約：全関手同型の等式。使われ方：元の指定導来合成子の計算式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E K : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] [_root_.SerrePositivity.DifferentialGraded.DGCategory R K] [Small.{u} K]
  (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.DifferentialGraded.RightModule R E) (_root_.SerrePositivity.DifferentialGraded.RightModule R K))
/-- 同じ指定 raw factor の端点輸送を明示すると、元の augmentation 比較の正方形は可換。 -/
lemma dgModuleAugmentationResolvedComparisonIso_rawFactor
    (hq : ∀ X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F,
      _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R K (H.onClosed.map X.augmentation)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationResolvedComparisonIso R C E K F H hq ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) K
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget R C E F).comp H)) rfl
        (congrArg (fun m => m ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R K) K
          (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R K)))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget R C E F) H)) =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) K
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).comp H)) rfl
        (congrArg (fun m => m ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R K) K
          (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R K)))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F) H)) ≪≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationRawFactorIso R C E K F H hq := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso_precomp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso_precomp]
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationResolvedComparisonIso _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationRawFactorIso
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoPostcompConjugate
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
