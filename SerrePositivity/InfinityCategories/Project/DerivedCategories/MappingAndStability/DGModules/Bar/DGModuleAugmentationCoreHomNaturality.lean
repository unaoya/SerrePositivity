module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleRawOutputPrecompHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Bar.DGModuleAugmentationRawHomNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Bar.DGModuleAugmentationRawFactorCore
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomSquareTransport
/-!
概要：元の augmentation の自然性を、二射影と同じ指定入力切断の表示へ移す。
方針：同じ全関手射の端点輸送と二段前合成の整合性を保つ。
規約：指定比較と切断・計算上限を変更しない。使われ方：元の κ の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
variable (R : Type u) [CommRing R] (E K : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] [_root_.SerrePositivity.DifferentialGraded.DGCategory R K] [Small.{u} K]
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R K) K
  (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R K))
variable (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
local notation "T" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F
local notation "I" => dgFullSubcategoryInclusion R (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E F
local notation "P0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F
local notation "A0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F
local notation "B0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget R C E F
lemma dgModuleAugmentationRawFactorCoreIso_hom_naturality
    (H0 H1 : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.DifferentialGraded.RightModule R E) (_root_.SerrePositivity.DifferentialGraded.RightModule R K))
    (hq0 : ∀ X : T, _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R K (H0.onClosed.map X.augmentation))
    (hq1 : ∀ X : T, _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R K (H1.onClosed.map X.augmentation))
    (d : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H0 ≫ L) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H1 ≫ L)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationRawFactorCoreIso R C E K F H0 hq0).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F.comp H0) ≫ L)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F.comp H1) ≫ L) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map P0)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleRawOutputPrecompHom R E K C F H0 H1 d) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((I).comp H0) ≫ L)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((I).comp H1) ≫ L) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleRawOutputPrecompHom R E K (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) I H0 H1 d) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationRawFactorCoreIso R C E K F H1 hq1).hom := by
  have hs (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.DifferentialGraded.RightModule R E) (_root_.SerrePositivity.DifferentialGraded.RightModule R K)) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((I).comp H) ≫ L =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map A0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H ≫ L := by
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Category.assoc]
  have ht (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.DifferentialGraded.RightModule R E) (_root_.SerrePositivity.DifferentialGraded.RightModule R K)) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map P0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F.comp H) ≫ L =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map B0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H ≫ L := by
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Category.assoc]
  have hc0 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq_of_endpoint_heq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationRawFactorCoreIso R C E K F H0 hq0)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationRawFactorIso R C E K F H0 hq0) (hs H0) (ht H0)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationRawFactorCoreIso_heq R C E K F H0 hq0)
  have hc1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq_of_endpoint_heq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationRawFactorCoreIso R C E K F H1 hq1)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationRawFactorIso R C E K F H1 hq1) (hs H1) (ht H1)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationRawFactorCoreIso_heq R C E K F H1 hq1)
  have hr := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleRawOutputPrecompHom_precomp_heq R E K C T F P0 H0 H1 d
  have hq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleRawOutputPrecompHom_precomp_heq R E K
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) T I G H0 H1 d
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_two_two_eq_of_heq
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((I).comp H0) ≫ L)
    (g := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map P0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F.comp H0) ≫ L)
    (h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((I).comp H1) ≫ L)
    (k := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map P0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F.comp H1) ≫ L)
    _ _ _ _ _ _ _ _ (hs H0) (ht H0) (hs H1) (ht H1) hc0 hr hq hc1
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationRawFactorIso_hom_naturality R C E K F H0 H1 hq0 hq1 d)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
