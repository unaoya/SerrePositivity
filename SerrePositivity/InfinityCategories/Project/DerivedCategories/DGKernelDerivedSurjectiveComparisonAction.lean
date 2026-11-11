module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelDerivedChangeRawValue
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
lemma dgKernelDerivedInfinity_surjective_comparison_hom
    (hf : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R E D f)
    (hs : ∀ (e : E) (d : D) (j : ℤ),
      Function.Surjective (((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.valueEvaluation R E D e d).map f).f j)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_surjective_quasiIso R D E f hf hs).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map f := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_changeIso_hom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelMap R D E f)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelMap_degree_surjective R D E f hs)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelMap_quasiIso R D E f hf)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelMap_hom_naturality R D E f)
  have hm := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelMap_resolved_raw_heq R D E f
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG] at h hm
  have hme := eq_of_heq hm
  rw [hme] at h
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_surjective_quasiIso,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedRawFactorIso,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolvedRawFunctorHomFunctor, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Category.assoc] using! h
end SerrePositivity.InfinityCategories.Project.DerivedCategories
