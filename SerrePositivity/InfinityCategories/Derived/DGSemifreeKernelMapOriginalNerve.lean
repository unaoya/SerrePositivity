module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedChangeHom
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedQuasiIsoMapInvertible
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  {P Q : BimoduleCategory R E D} (f : P ⟶ Q)
local notation "I" => dgFullSubcategoryInclusion R (RightModule R D) (dgModuleSemifreeProperty R D)
local notation "b" => BimoduleTensor.composeMap R E D (SemifreeDGModules R D) f
  (𝟙 (BimoduleCategory.of R D (SemifreeDGModules R D) I))
local notation "FP" => dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D P)
local notation "FQ" => dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D Q)
lemma dgSemifreeKernelMap_original_strict_heq :
    HEq (dgModuleResolutionChangeIdentityOriginalNatTrans R (SemifreeDGModules R D) E FP FQ
      (dgSemifreeKernelMap R D E f) (dgSemifreeKernelMap_hom_naturality R D E f))
      (dgBimoduleMapStrictNatTrans R E (SemifreeDGModules R D) b) := by
  have hp := dgKernelTensor_postcomp_bimodule_eq R D E (SemifreeDGModules R D) I
    (BimoduleCategory.underlying R E D P)
  have hq := dgKernelTensor_postcomp_bimodule_eq R D E (SemifreeDGModules R D) I
    (BimoduleCategory.underlying R E D Q)
  apply dgStrictNatTrans_heq_of_functor_eq _ _ hp hq
  intro M
  apply heq_of_eq
  change cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (dgSemifreeKernelMap R D E f M)) =
    cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
      ((BimoduleCategory.evaluation R E (SemifreeDGModules R D) M).map b))
  rw [dgSemifreeKernelBimoduleMap_evaluation R D E f M]
  rfl
lemma dgSemifreeKernelMap_original_nerve_heq :
    HEq (dgStrictNatTransNerveHom R (SemifreeDGModules R D) (RightModule R E)
      (dgModuleResolutionChangeIdentityOriginalNatTrans R (SemifreeDGModules R D) E FP FQ
        (dgSemifreeKernelMap R D E f) (dgSemifreeKernelMap_hom_naturality R D E f)))
      (functorHomPrecomp
        (dgNerve.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D P)))
        (dgNerve.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D Q)))
        (dgNerve.map I) ((dgKernelTensorFunctorHomFunctor R D E).map f)) := by
  have hp := dgKernelTensor_postcomp_bimodule_eq R D E (SemifreeDGModules R D) I
    (BimoduleCategory.underlying R E D P)
  have hq := dgKernelTensor_postcomp_bimodule_eq R D E (SemifreeDGModules R D) I
    (BimoduleCategory.underlying R E D Q)
  have hh := dgStrictNatTransNerveHom_heq_of_functor_eq _ _ hp hq
    (dgSemifreeKernelMap_original_strict_heq R D E f)
  have hn := dgKernelBimoduleMap_precomp_nerve_hom_heq R D E (SemifreeDGModules R D) f I
  have hm := functorHomPrecomp_map_heq
    (dgNerve.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D P)))
    (dgNerve.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D Q)))
    (dgNerve.map I) ((dgKernelTensorFunctorHomFunctor R D E).map f)
  exact hh.trans (hn.trans hm.symm)
end SerrePositivity.InfinityCategories
