module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FunctorComparisons.DGBimoduleIsoNerve
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelDerivedInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedProjectiveComparison
public import SerrePositivity.DifferentialGraded.Tensor.Triple
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition
/-!
概要：同じ対角双加群の実導来作用を、元の導来 ∞ 圏の恒等関手へ比較する。
方針：全 Hom 自然な実単位子を nerve に移し、同じ出力分解の包含比較から回収する。
規約：元の dg 圏の Hom の平坦性を仮定しない。使われ方：一般双加群作用の単位比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- 元の対角 tensor の生の nerve 作用は、同じ全 Hom 自然な単位子で恒等と同型。 -/
def dgKernelIdentityNerveIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D D (Bimodule.diagonal R D)))
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R D)) := by
  have e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleIsoNerve R D (RightModule R D)
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.leftBimoduleUnitIso R D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D)))
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_id] using! e
/-- 対角 tensor の出力は、元の入力が射影的なら射影的。 -/
lemma dgKernelIdentity_tensor_projective (M : _root_.SerrePositivity.DifferentialGraded.RightModule R D)
    (hM : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D ((Morita.kernelTensor R D D (Bimodule.diagonal R D)).obj M) := by
  let e := (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.evaluation R D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) M).mapIso
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.leftBimoduleUnitIso R D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D)))
  exact _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective_of_iso R D e.symm hM
/-- 同じ対角双加群の実導来作用は、元の実導来 ∞ 圏の恒等と全関手同型。 -/
def dgKernelDerivedInfinity_identityIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D D (Bimodule.diagonal R D))
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)) := by
  let I := dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)
  have e1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_inclusionIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) D
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D D (Bimodule.diagonal R D))
    (fun M => dgKernelIdentity_tensor_projective R D M.val (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModule_isProjective R D M))
  have e2 := (dgKernelIdentityNerveIso R D).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map I)
  have H : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D D (Bimodule.diagonal R D) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map I)
      ((𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map I) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp,
      Category.comp_id, Category.id_comp] using! (e1 ≪≫ e2)
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModulesInclusion_isFullyFaithful R D).preimageFunctorIso H
end SerrePositivity.InfinityCategories.Project.DerivedCategories
