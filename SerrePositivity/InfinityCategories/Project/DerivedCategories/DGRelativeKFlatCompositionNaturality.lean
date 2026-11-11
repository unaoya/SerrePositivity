module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCompositionNerveIsoNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatBimoduleIsoWhisker
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatCompatibilityInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoLiftedPathReflection
/-!
概要：K-flat の元の指定合成比較の双加群同型に対する二変数自然性を証明する。
方針：各指定同型と前後合成を包含後に回収し、元の通常比較の自然性を反映する。
規約：原 Hom の平坦性を追加しない。使われ方：元の κ の自然性と左単位三角式。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E F : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R F] [Small.{u} F]
private lemma pair_inclusion (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R F E)
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P) (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R F E Q) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P hP ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R E F Q hQ) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R F = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E F Q)) := by
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion, Category.assoc]
variable {P P' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} {Q Q' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R F E}
local notation "P₀" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P
local notation "P₁" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P'
local notation "Q₀" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q
local notation "Q₁" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q'
/-- 元の K-flat 指定合成比較は、同じ二つの双加群同型の作用に自然。 -/
lemma dgRelativeKFlatKernelCompositionIso_naturality (f : P ≅ P') (g : Q ≅ Q')
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P₀) (hP' : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P₁)
    (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R F E Q₀) (hQ' : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R F E Q₁) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R D E F P₀ Q₀ hP hQ ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleIso R D F
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelBimoduleComposeIso R D E F f g)
        (_root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R F E D Q₀ P₀ hQ hP)
        (_root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R F E D Q₁ P₁ hQ' hP') =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleIso R D E f hP hP').postcomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R E F Q₀ hQ) ≪≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleIso R E F g hQ hQ').precomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P₁ hP') ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R D E F P₁ Q₁ hP' hQ' := by
  have hf := pair_inclusion R D E F P₀ Q₀ hP hQ
  have hg := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion R D F (BimoduleTensor.compose R F E D Q₀ P₀)
    (_root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R F E D Q₀ P₀ hQ hP)
  have hh := pair_inclusion R D E F P₁ Q₀ hP' hQ
  have ht := pair_inclusion R D E F P₁ Q₁ hP' hQ'
  have hk := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion R D F (BimoduleTensor.compose R F E D Q₁ P₁)
    (_root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R F E D Q₁ P₁ hQ' hP')
  have he := congrArg (fun e => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso_naturality R D E F f g)
  simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans] at he
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_two_three_reflect_postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R F)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R F)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleRelativeKFlatVertex R F)) _ _ _ _ _ _ _ _ _ _ hf hg hh ht hk
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso_inclusion_heq R D E F P₀ Q₀ hP hQ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleIso_inclusion_heq R D F
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelBimoduleComposeIso R D E F f g)
      (_root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R F E D Q₀ P₀ hQ hP)
      (_root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R F E D Q₁ P₁ hQ' hP'))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleIso_postcomp_inclusion_heq R D E F f hP hP' Q₀ hQ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleIso_precomp_inclusion_heq R D E F g hQ hQ' P₁ hP')
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso_inclusion_heq R D E F P₁ Q₁ hP' hQ') he
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
