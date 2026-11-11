module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelBimoduleIsoRawFactor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatKernelBimoduleIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoLiftedRestrictionResolution
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatResolutionLocalization
/-!
概要：同じ K-flat 双加群同型の作用を、半自由入力上の元の raw 比較へ戻す。
方針：実包含の可換式・指定同型の異種等式・同じ出力分解を保つ。
規約：元の指定値を変更しない。使われ方：制限比較 ρ と ξ の自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 元の半自由入力の raw 比較は、同じ通常作用の実制限の指定値を保つ。 -/
lemma dgKernelBimoduleIsoSemifreeNerve_heq {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (e : P ≅ Q) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelBimoduleIsoSemifreeNerve R D E e)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso R D E e).precomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R D)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)))) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelBimoduleIsoSemifreeNerve, Eq.mpr]
  rfl
/-- K-flat の双加群同型作用の分解・半自由制限は、元の同じ raw 比較の分解像。 -/
lemma dgRelativeKFlatKernelBimoduleIso_semifree_resolution_heq
    {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (e : P ≅ Q)
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P))
    (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D Q)) :
    HEq (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleIso R D E e hP hQ).postcomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R E)).precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelBimoduleIsoSemifreeNerve R D E e).postcomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E)))) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_lifted_restriction_resolution_heq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleIso R D E e hP hQ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso R D E e)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion R D E (BimoduleCategory.underlying R E D P) hP).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion R D E (BimoduleCategory.underlying R E D Q) hQ).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleIso_inclusion_heq R D E e hP hQ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve_inclusion R D)
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D P)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D Q)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D Q)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
  have hh := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelBimoduleIsoSemifreeNerve R D E e)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso R D E e).precomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)))) hf hg
    (dgKernelBimoduleIsoSemifreeNerve_heq R D E e).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E)))
  exact h.trans hh
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
