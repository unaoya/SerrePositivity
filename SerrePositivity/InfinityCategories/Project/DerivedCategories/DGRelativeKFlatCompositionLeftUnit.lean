module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCompositionNerveLeftUnit
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatKernelUnit
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatCompatibilityInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatKernelBimoduleIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoLiftedWhiskerSquare
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoLiftedPathReflection
/-!
概要：元の K-flat 合成比較の左単位三角式を証明する。
方針：通常 nerve の同じ三角式を完全充満包含から反映する。
規約：指定比較と元の単位子を保つ。使われ方：導来 kernel の coherence。
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
  (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P)
local notation "I" => _root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R E
local notation "IP" => _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R E E D I P
local notation "hI" => _root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal_rightRelativeKFlat R E
local notation "hIP" => _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R E E D I P hI hP
include hP in
/-- 指定 K-flat 合成比較と同じ左単位子の作用は、元の単位の制限に一致。 -/
lemma dgRelativeKFlatKernelCompositionIso_left_unit :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R D E E P I hP hI ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleIso R D E
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.leftBimoduleUnitIso R E D P) hIP hP =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelIdentityIso R E).precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P hP) := by
  have hf : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P hP ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R E E I hI) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R E =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E E I)) := by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion, Category.assoc]
  have hg := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion R D E IP hIP
  have hk := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion R D E P hP
  have hi : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R E ≫ 𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R E) =
      𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleNerve R E) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R E := by
    rw [Category.comp_id, Category.id_comp]
  have hq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_lifted_precomp_square (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelIdentityIso R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelIdentityNerveIso R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P hP)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion R E E I hI).symm hi
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelIdentityIso_inclusion_heq R E) hk
  have he := congrArg (fun e => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso_left_unit R D E P)
  simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans] at he
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_two_one_reflect_postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R E)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleRelativeKFlatVertex R E)) _ _ _ _ _ _ hf hg hk
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso_inclusion_heq R D E E P I hP hI)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleIso_inclusion_heq R D E
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.leftBimoduleUnitIso R E D P) hIP hP) hq he
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
