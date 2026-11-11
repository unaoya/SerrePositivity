module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedChangeHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelDerivedQuasiIsoMapInvertible
/-!
概要：選択済みの双加群比較を、同じ実導来射作用へ照合する。
方針：元の半自由 tensor 射・厳密変換・全 nerve 像を同じ raw factor へ戻す。
規約：指定比較の値を変更しない。使われ方：模型変更の全自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (f : P ⟶ Q)
local notation "I" => dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)
local notation "b" => BimoduleTensor.composeMap R E D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) f
  (𝟙 (BimoduleCategory.of R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) I))
local notation "FP" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D P)
local notation "FQ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D Q)
lemma dgSemifreeKernelMap_original_strict_heq :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityOriginalNatTrans R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E FP FQ
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelMap R D E f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelMap_hom_naturality R D E f))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleMapStrictNatTrans R E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) b) := by
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensor_postcomp_bimodule_eq R D E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) I
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P)
  have hq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensor_postcomp_bimodule_eq R D E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) I
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D Q)
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_heq_of_functor_eq _ _ hp hq
  intro M
  apply heq_of_eq
  change cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelMap R D E f M)) =
    _root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex R)
      ((BimoduleCategory.evaluation R E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) M).map b))
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelBimoduleMap_evaluation R D E f M]
  rfl
lemma dgSemifreeKernelMap_original_nerve_heq :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) (RightModule R E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityOriginalNatTrans R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E FP FQ
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelMap R D E f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelMap_hom_naturality R D E f)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D P)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D Q)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map I) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R D E).map f)) := by
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensor_postcomp_bimodule_eq R D E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) I
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P)
  have hq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensor_postcomp_bimodule_eq R D E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) I
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D Q)
  have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_heq_of_functor_eq _ _ hp hq
    (dgSemifreeKernelMap_original_strict_heq R D E f)
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelBimoduleMap_precomp_nerve_hom_heq R D E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) f I
  have hm := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_map_heq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D P)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D Q)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map I) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R D E).map f)
  exact hh.trans (hn.trans hm.symm)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
