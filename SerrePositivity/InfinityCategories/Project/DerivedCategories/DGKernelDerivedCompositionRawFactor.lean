module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelDerivedCompositionKFlat
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedCompositionRawFactorEq
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D E K : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R K] [Small.{u} K]
  (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R K E)
/-- 通常 tensor の同じ結合子を、半自由入力上の同じ実 nerve へ制限する。 -/
def dgKernelTensorCompositionSemifreeIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P).comp
      (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R E K Q)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D K (BimoduleTensor.compose R K E D Q P))) := by
  have e := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E K P Q).precomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)))
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Category.assoc] using! e
/-- 元の kernel 合成子の raw factor 計算は、同じ augmentation と通常 tensor の結合子。 -/
lemma dgKernelDerivedInfinity_compIso_rawFactor
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E K P Q hP ≪≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) K
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D K (BimoduleTensor.compose R K E D Q P)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) K
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R E K Q)).precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P) ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationRawFactorIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E K
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P) (Morita.kernelTensor R E K Q)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolutionAugmentation_tensor_quasiIso R D E K P Q hP) ≪≫
      (dgKernelTensorCompositionSemifreeIso R D E K P Q).postcomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K))) := by
  dsimp -zeta only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat]
  extract_lets C I F G H a er0 er b
  change (a ≪≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R C K (F.comp H) ≪≫
      er.postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R K) K
        (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R K))) ≪≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R C K G).symm)) ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R C K G = _
  simp only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_compositionIso_rawFactor R C E K F H
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolutionAugmentation_tensor_quasiIso R D E K P Q hP)
  rw [← Iso.trans_assoc, hc, Iso.trans_assoc]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
