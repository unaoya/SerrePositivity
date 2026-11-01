module
public import SerrePositivity.InfinityCategories.Derived.DGBimoduleIsoNerve
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedInfinity
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedProjectiveComparison
public import SerrePositivity.DifferentialGraded.Tensor.Triple
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulPostcomposition
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 元の対角 tensor の生の nerve 作用は、同じ全 Hom 自然な単位子で恒等と同型。 -/
def dgKernelIdentityNerveIso :
    FunctorIso (dgNerve.map (Morita.kernelTensor R D D (Bimodule.diagonal R D)))
      (𝟙 (dgModuleNerve R D)) := by
  have e := dgBimoduleIsoNerve R D (RightModule R D)
    (BimoduleTensor.leftBimoduleUnitIso R D (RightModule R D) (DGFunctor.id (RightModule R D)))
  simpa only [dgNerve.map_id] using! e
/-- 対角 tensor の出力は、元の入力が射影的なら射影的。 -/
lemma dgKernelIdentity_tensor_projective (M : RightModule R D)
    (hM : dgModuleProjectiveProperty R D M) :
    dgModuleProjectiveProperty R D ((Morita.kernelTensor R D D (Bimodule.diagonal R D)).obj M) := by
  let e := (BimoduleCategory.evaluation R D (RightModule R D) M).mapIso
    (BimoduleTensor.leftBimoduleUnitIso R D (RightModule R D) (DGFunctor.id (RightModule R D)))
  exact moduleHomotopicallyProjective_of_iso R D e.symm hM
/-- 同じ対角双加群の実導来作用は、元の実導来 ∞ 圏の恒等と全関手同型。 -/
def dgKernelDerivedInfinity_identityIso :
    FunctorIso (dgKernelDerivedInfinity R D D (Bimodule.diagonal R D))
      (𝟙 (dgModuleDerivedInfinityCategory R D)) := by
  let I := dgFullSubcategoryInclusion R (RightModule R D) (dgModuleSemifreeProperty R D)
  have e1 := dgModuleResolvedInfinity_inclusionIso R (SemifreeDGModules R D) D
    (dgSemifreeKernelModuleDG R D D (Bimodule.diagonal R D))
    (fun M => dgKernelIdentity_tensor_projective R D M.val (dgSemifreeModule_isProjective R D M))
  have e2 := (dgKernelIdentityNerveIso R D).precomp (dgNerve.map I)
  have H : FunctorIso (dgKernelDerivedInfinity R D D (Bimodule.diagonal R D) ≫ dgNerve.map I)
      ((𝟙 (dgModuleDerivedInfinityCategory R D)) ≫ dgNerve.map I) := by
    simpa only [dgSemifreeKernelModuleDG, dgNerve.map_comp,
      Category.comp_id, Category.id_comp] using! (e1 ≪≫ e2)
  exact (dgSemifreeModulesInclusion_isFullyFaithful R D).preimageFunctorIso H
end SerrePositivity.InfinityCategories
