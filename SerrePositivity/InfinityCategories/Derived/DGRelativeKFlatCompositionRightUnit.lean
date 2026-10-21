module
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatCompatibilityInclusion
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelBimoduleIso
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelUnit
public import SerrePositivity.InfinityCategories.Derived.DGKernelCompositionNerveRightUnit
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoLiftedWhiskerSquare
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoLiftedPathReflection
/-!
概要：元の K-flat kernel 合成比較の右単位三角式を、全関手同型として証明する。
方針：同じ通常単位三角の包含への制限から、完全充満性で等式を反映する。
規約：原 Hom の平坦性を追加しない。使われ方：元の導来合成子の単位 coherence。
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
variable (P : Bimodule R E D) (hP : Bimodule.rightRelativeKFlat R E D P)
local notation "hΔ" => Bimodule.diagonal_rightRelativeKFlat R D
local notation "hPΔ" => Bimodule.rightRelativeKFlat_compose R E D D P
  (Bimodule.diagonal R D) hP hΔ
/-- 元の K-flat 合成比較と右単位子の作用は、元の K-flat 単位の後合成と一致する。 -/
lemma dgRelativeKFlatKernelCompositionIso_right_unit :
    dgRelativeKFlatKernelCompositionIso R D D E (Bimodule.diagonal R D) P hΔ hP ≪≫
      dgRelativeKFlatKernelBimoduleIso R D E
        (BimoduleTensor.rightBimoduleUnitIso R E D P) hPΔ hP =
    (dgRelativeKFlatKernelIdentityIso R D).postcomp (dgRelativeKFlatKernelNerve R D E P hP) := by
  have hf : (dgRelativeKFlatKernelNerve R D D (Bimodule.diagonal R D) hΔ ≫
      dgRelativeKFlatKernelNerve R D E P hP) ≫ dgRelativeKFlatModuleInclusion R E =
      dgRelativeKFlatModuleInclusion R D ≫
        (dgNerve.map (Morita.kernelTensor R D D (Bimodule.diagonal R D)) ≫
          dgNerve.map (Morita.kernelTensor R D E P)) := by
    rw [Category.assoc, dgRelativeKFlatKernelNerve_inclusion, ← Category.assoc,
      dgRelativeKFlatKernelNerve_inclusion, Category.assoc]
  have hg := dgRelativeKFlatKernelNerve_inclusion R D E
    (BimoduleTensor.compose R E D D P (Bimodule.diagonal R D)) hPΔ
  have hk := dgRelativeKFlatKernelNerve_inclusion R D E P hP
  have hi : dgRelativeKFlatModuleInclusion R D ≫ 𝟙 (dgModuleNerve R D) =
      𝟙 (dgRelativeKFlatModuleNerve R D) ≫ dgRelativeKFlatModuleInclusion R D := by
    rw [Category.id_comp, Category.comp_id]
  have hq := functorIso_lifted_postcomp_square
    (dgRelativeKFlatKernelIdentityIso R D) (dgKernelIdentityNerveIso R D)
    (dgRelativeKFlatModuleInclusion R D) (dgRelativeKFlatModuleInclusion R D)
    (dgRelativeKFlatKernelNerve R D E P hP) (dgRelativeKFlatModuleInclusion R E)
    (dgNerve.map (Morita.kernelTensor R D E P))
    (dgRelativeKFlatKernelNerve_inclusion R D D (Bimodule.diagonal R D) hΔ).symm hi
    (dgRelativeKFlatKernelIdentityIso_inclusion_heq R D) hk
  have he := congrArg (fun e => FunctorIso.precomp e (dgRelativeKFlatModuleInclusion R D))
    (dgKernelTensorCompositionNerveIso_right_unit R D E P)
  simp only [F2.functorIso_precomp_trans] at he
  exact functorIso_two_one_reflect_postcomp (dgRelativeKFlatModuleInclusion R E)
    (isFullyFaithful_fullSubcomplexOnVertices_ι (dgModuleNerve R E)
      (dgModuleRelativeKFlatVertex R E)) _ _ _ _ _ _ hf hg hk
    (dgRelativeKFlatKernelCompositionIso_inclusion_heq R D D E
      (Bimodule.diagonal R D) P hΔ hP)
    (dgRelativeKFlatKernelBimoduleIso_inclusion_heq R D E
      (BimoduleTensor.rightBimoduleUnitIso R E D P) hPΔ hP) hq he
end
end SerrePositivity.InfinityCategories
