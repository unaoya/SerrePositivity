module
public import SerrePositivity.InfinityCategories.Derived.DGKernelCompositionNerveLeftUnit
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelUnit
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatCompatibilityInclusion
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelBimoduleIso
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoLiftedWhiskerSquare
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoLiftedPathReflection
/-!
概要：元の K-flat 合成比較の左単位三角式を証明する。
方針：通常 nerve の同じ三角式を完全充満包含から反映する。
規約：指定比較と元の単位子を保つ。使われ方：導来 kernel の coherence。
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
  (P : Bimodule R E D) (hP : Bimodule.rightRelativeKFlat R E D P)
local notation "I" => Bimodule.diagonal R E
local notation "IP" => BimoduleTensor.compose R E E D I P
local notation "hI" => Bimodule.diagonal_rightRelativeKFlat R E
local notation "hIP" => Bimodule.rightRelativeKFlat_compose R E E D I P hI hP
include hP in
/-- 指定 K-flat 合成比較と同じ左単位子の作用は、元の単位の制限に一致。 -/
lemma dgRelativeKFlatKernelCompositionIso_left_unit :
    dgRelativeKFlatKernelCompositionIso R D E E P I hP hI ≪≫
      dgRelativeKFlatKernelBimoduleIso R D E
        (BimoduleTensor.leftBimoduleUnitIso R E D P) hIP hP =
    (dgRelativeKFlatKernelIdentityIso R E).precomp (dgRelativeKFlatKernelNerve R D E P hP) := by
  have hf : (dgRelativeKFlatKernelNerve R D E P hP ≫
      dgRelativeKFlatKernelNerve R E E I hI) ≫ dgRelativeKFlatModuleInclusion R E =
      dgRelativeKFlatModuleInclusion R D ≫
        (dgNerve.map (Morita.kernelTensor R D E P) ≫
          dgNerve.map (Morita.kernelTensor R E E I)) := by
    rw [Category.assoc, dgRelativeKFlatKernelNerve_inclusion, ← Category.assoc,
      dgRelativeKFlatKernelNerve_inclusion, Category.assoc]
  have hg := dgRelativeKFlatKernelNerve_inclusion R D E IP hIP
  have hk := dgRelativeKFlatKernelNerve_inclusion R D E P hP
  have hi : dgRelativeKFlatModuleInclusion R E ≫ 𝟙 (dgModuleNerve R E) =
      𝟙 (dgRelativeKFlatModuleNerve R E) ≫ dgRelativeKFlatModuleInclusion R E := by
    rw [Category.comp_id, Category.id_comp]
  have hq := functorIso_lifted_precomp_square (dgRelativeKFlatKernelIdentityIso R E)
    (dgKernelIdentityNerveIso R E) (dgRelativeKFlatModuleInclusion R E)
    (dgRelativeKFlatModuleInclusion R E) (dgRelativeKFlatKernelNerve R D E P hP)
    (dgNerve.map (Morita.kernelTensor R D E P)) (dgRelativeKFlatModuleInclusion R D)
    (dgRelativeKFlatKernelNerve_inclusion R E E I hI).symm hi
    (dgRelativeKFlatKernelIdentityIso_inclusion_heq R E) hk
  have he := congrArg (fun e => FunctorIso.precomp e (dgRelativeKFlatModuleInclusion R D))
    (dgKernelTensorCompositionNerveIso_left_unit R D E P)
  simp only [F2.functorIso_precomp_trans] at he
  exact functorIso_two_one_reflect_postcomp (dgRelativeKFlatModuleInclusion R E)
    (isFullyFaithful_fullSubcomplexOnVertices_ι (dgModuleNerve R E)
      (dgModuleRelativeKFlatVertex R E)) _ _ _ _ _ _ hf hg hk
    (dgRelativeKFlatKernelCompositionIso_inclusion_heq R D E E P I hP hI)
    (dgRelativeKFlatKernelBimoduleIso_inclusion_heq R D E
      (BimoduleTensor.leftBimoduleUnitIso R E D P) hIP hP) hq he
end
end SerrePositivity.InfinityCategories
