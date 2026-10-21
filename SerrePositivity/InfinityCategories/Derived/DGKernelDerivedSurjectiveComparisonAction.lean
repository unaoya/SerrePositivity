module
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedChangeRawValue
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
lemma dgKernelDerivedInfinity_surjective_comparison_hom
    (hf : BimoduleCategory.quasiIso R E D f)
    (hs : ∀ (e : E) (d : D) (j : ℤ),
      Function.Surjective (((BimoduleCategory.valueEvaluation R E D e d).map f).f j)) :
    (dgKernelDerivedInfinity_mapIso_of_surjective_quasiIso R D E f hf hs).hom =
      (dgKernelDerivedFunctorHomFunctor R D E).map f := by
  have h := dgModuleResolvedInfinity_changeIso_hom R (SemifreeDGModules R D) E
    (dgSemifreeKernelMap R D E f)
    (dgSemifreeKernelMap_degree_surjective R D E f hs)
    (dgSemifreeKernelMap_quasiIso R D E f hf)
    (dgSemifreeKernelMap_hom_naturality R D E f)
  have hm := dgSemifreeKernelMap_resolved_raw_heq R D E f
  simp only [dgSemifreeKernelModuleDG] at h hm
  have hme := eq_of_heq hm
  rw [hme] at h
  simpa only [dgKernelDerivedInfinity_mapIso_of_surjective_quasiIso,
    dgKernelDerivedFunctorHomFunctor, dgKernelDerivedRawFactorIso,
    dgKernelResolvedRawFunctorHomFunctor, dgSemifreeKernelModuleDG,
    dgNerve.map_comp, Category.assoc] using! h
end SerrePositivity.InfinityCategories
