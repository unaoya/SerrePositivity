module
public import SerrePositivity.InfinityCategories.Derived.DGKernelBimoduleIsoRawFactor
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelBimoduleIso
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoLiftedRestrictionResolution
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatResolutionLocalization
/-!
概要：同じ K-flat 双加群同型の作用を、半自由入力上の元の raw 比較へ戻す。
方針：実包含の可換式・指定同型の異種等式・同じ出力分解を保つ。
規約：元の指定値を変更しない。使われ方：制限比較 ρ と ξ の自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 元の半自由入力の raw 比較は、同じ通常作用の実制限の指定値を保つ。 -/
lemma dgKernelBimoduleIsoSemifreeNerve_heq {P Q : BimoduleCategory R E D} (e : P ≅ Q) :
    HEq (dgKernelBimoduleIsoSemifreeNerve R D E e)
      ((dgKernelTensorIsoNerveOfBimoduleIso R D E e).precomp
        (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
          (dgModuleSemifreeProperty R D)))) := by
  simp only [dgKernelBimoduleIsoSemifreeNerve, Eq.mpr]
  rfl
/-- K-flat の双加群同型作用の分解・半自由制限は、元の同じ raw 比較の分解像。 -/
lemma dgRelativeKFlatKernelBimoduleIso_semifree_resolution_heq
    {P Q : BimoduleCategory R E D} (e : P ≅ Q)
    (hP : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D P))
    (hQ : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D Q)) :
    HEq (((dgRelativeKFlatKernelBimoduleIso R D E e hP hQ).postcomp
      (dgRelativeKFlatResolution R E)).precomp (dgSemifreeToRelativeKFlatNerve R D))
      ((dgKernelBimoduleIsoSemifreeNerve R D E e).postcomp
        (dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E)))) := by
  have h := functorIso_lifted_restriction_resolution_heq
    (dgRelativeKFlatKernelBimoduleIso R D E e hP hQ)
    (dgKernelTensorIsoNerveOfBimoduleIso R D E e)
    (dgRelativeKFlatModuleInclusion R D) (dgRelativeKFlatModuleInclusion R E)
    (dgSemifreeToRelativeKFlatNerve R D)
    (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
      (dgModuleSemifreeProperty R D)))
    (dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E)))
    (dgRelativeKFlatKernelNerve_inclusion R D E (BimoduleCategory.underlying R E D P) hP).symm
    (dgRelativeKFlatKernelNerve_inclusion R D E (BimoduleCategory.underlying R E D Q) hQ).symm
    (dgRelativeKFlatKernelBimoduleIso_inclusion_heq R D E e hP hQ)
    (dgSemifreeToRelativeKFlatNerve_inclusion R D)
  have hf : dgNerve.map (dgSemifreeKernelModuleDG R D E
      (BimoduleCategory.underlying R E D P)) =
      dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
        (dgModuleSemifreeProperty R D)) ≫
          dgNerve.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D P)) := by
    rw [dgSemifreeKernelModuleDG, dgNerve.map_comp]
  have hg : dgNerve.map (dgSemifreeKernelModuleDG R D E
      (BimoduleCategory.underlying R E D Q)) =
      dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
        (dgModuleSemifreeProperty R D)) ≫
          dgNerve.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D Q)) := by
    rw [dgSemifreeKernelModuleDG, dgNerve.map_comp]
  have hh := F2.functorIso_postcomp_heq_of_heq (dgKernelBimoduleIsoSemifreeNerve R D E e)
    ((dgKernelTensorIsoNerveOfBimoduleIso R D E e).precomp
      (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
        (dgModuleSemifreeProperty R D)))) hf hg
    (dgKernelBimoduleIsoSemifreeNerve_heq R D E e).symm
    (dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E)))
  exact h.trans hh
end
end SerrePositivity.InfinityCategories
