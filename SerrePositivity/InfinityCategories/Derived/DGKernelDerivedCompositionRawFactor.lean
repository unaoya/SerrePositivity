module
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedCompositionKFlat
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedCompositionRawFactorEq
/-!
概要：元の指定 kernel 合成子を通常 tensor と同じ augmentation の経路で計算する。
方針：指定三項経路の raw factor 計算を適用し、末尾の出力比較を相殺する。
規約：元の指定合成子の値を保つ。使われ方：K-flat 上の通常 tensor 経路との照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D E K : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R K] [Small.{u} K]
  (P : Bimodule R E D) (Q : Bimodule R K E)
/-- 通常 tensor の同じ結合子を、半自由入力上の同じ実 nerve へ制限する。 -/
def dgKernelTensorCompositionSemifreeIso :
    FunctorIso (dgNerve.map ((dgSemifreeKernelModuleDG R D E P).comp
      (Morita.kernelTensor R E K Q)))
      (dgNerve.map (dgSemifreeKernelModuleDG R D K (BimoduleTensor.compose R K E D Q P))) := by
  have e := (dgKernelTensorCompositionNerveIso R D E K P Q).precomp
    (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleSemifreeProperty R D)))
  simpa only [dgSemifreeKernelModuleDG, dgNerve.map_comp, Category.assoc] using! e
/-- 元の kernel 合成子の raw factor 計算は、同じ augmentation と通常 tensor の結合子。 -/
lemma dgKernelDerivedInfinity_compIso_rawFactor
    (hP : Bimodule.rightRelativeKFlat R E D P) :
    dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E K P Q hP ≪≫
        dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R D) K
          (dgSemifreeKernelModuleDG R D K (BimoduleTensor.compose R K E D Q P)) =
      (dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R E) K
        (dgSemifreeKernelModuleDG R E K Q)).precomp (dgKernelDerivedInfinity R D E P) ≪≫
      dgModuleResolvedAugmentationRawFactorIso R (SemifreeDGModules R D) E K
        (dgSemifreeKernelModuleDG R D E P) (Morita.kernelTensor R E K Q)
        (dgKernelResolutionAugmentation_tensor_quasiIso R D E K P Q hP) ≪≫
      (dgKernelTensorCompositionSemifreeIso R D E K P Q).postcomp
        (dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K))) := by
  dsimp -zeta only [dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat]
  extract_lets C I F G H a er0 er b
  change (a ≪≫ (dgModuleResolvedInfinity_rawFactorIso R C K (F.comp H) ≪≫
      er.postcomp (dgModuleResolvedInfinity R (RightModule R K) K
        (DGFunctor.id (RightModule R K))) ≪≫
      (dgModuleResolvedInfinity_rawFactorIso R C K G).symm)) ≪≫
      dgModuleResolvedInfinity_rawFactorIso R C K G = _
  simp only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
  have hc := dgModuleResolvedInfinity_compositionIso_rawFactor R C E K F H
    (dgKernelResolutionAugmentation_tensor_quasiIso R D E K P Q hP)
  rw [← Iso.trans_assoc, hc, Iso.trans_assoc]
  rfl
end SerrePositivity.InfinityCategories
