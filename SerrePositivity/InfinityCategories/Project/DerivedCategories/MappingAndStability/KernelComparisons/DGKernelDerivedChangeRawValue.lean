module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGSemifreeKernelMapOriginalNerve
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
lemma dgSemifreeKernelMap_resolved_raw_heq :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map FP) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map FQ)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) (RightModule R E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityOriginalNatTrans R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E FP FQ
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelMap R D E f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelMap_hom_naturality R D E f))))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolvedRawFunctorHomFunctor R D E).map f) := by
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map FP = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map I ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D E (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P)) := by
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
  have hq : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map FQ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map I ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D E (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D Q)) := by
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_heq _ _ hp hq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelMap_original_nerve_heq R D E f) _
lemma dgKernelDerivedRawFactorIso_module_heq (K : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedRawFactorIso R D E K)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D K))) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedRawFactorIso
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolvedRawFunctorHomFunctor, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
