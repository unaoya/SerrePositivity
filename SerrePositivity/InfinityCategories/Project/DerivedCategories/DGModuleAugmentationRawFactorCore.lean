module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleAugmentationRawFactorSquare
/-!
概要：同じ augmentation の通常後続像を、実二射影と通常合成の端点へ揃える。
方針：元の二つの dg 射影と nerve 合成の厳密等式だけで端点を輸送する。
規約：元の指定比較の値を保持する。使われ方：指定三項経路の raw factor 計算。
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
/-- 同じ augmentation の通常後続像を、実二射影の通常合成による両端へ輸送する。 -/
def dgModuleAugmentationRawFactorCoreIso
    (hq : ∀ X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F,
      _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R K (H.onClosed.map X.augmentation)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E F) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((dgFullSubcategoryInclusion R (RightModule R E)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E)).comp H) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F.comp H) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K))) := by
  refine _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationRawFactorIso R C E K F H hq) ?_ ?_
  · simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Category.assoc]
  · simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Category.assoc]
/-- 両射影による端点表示への輸送は、同じ元の指定比較を型付きで保持する。 -/
lemma dgModuleAugmentationRawFactorCoreIso_heq
    (hq : ∀ X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F,
      _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R K (H.onClosed.map X.augmentation)) :
    HEq (dgModuleAugmentationRawFactorCoreIso R C E K F H hq)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationRawFactorIso R C E K F H hq) := by
  unfold dgModuleAugmentationRawFactorCoreIso
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _
end SerrePositivity.InfinityCategories.Project.DerivedCategories
