module
public import SerrePositivity.InfinityCategories.Derived.DGKernelCompositionNerveIsoNaturality
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatBimoduleIsoWhisker
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatCompatibilityInclusion
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoLiftedPathReflection
/-!
概要：K-flat の元の指定合成比較の双加群同型に対する二変数自然性を証明する。
方針：各指定同型と前後合成を包含後に回収し、元の通常比較の自然性を反映する。
規約：原 Hom の平坦性を追加しない。使われ方：元の κ の自然性と左単位三角式。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E F : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R F] [Small.{u} F]
private lemma pair_inclusion (P : Bimodule R E D) (Q : Bimodule R F E)
    (hP : Bimodule.rightRelativeKFlat R E D P) (hQ : Bimodule.rightRelativeKFlat R F E Q) :
    (dgRelativeKFlatKernelNerve R D E P hP ≫ dgRelativeKFlatKernelNerve R E F Q hQ) ≫
      dgRelativeKFlatModuleInclusion R F = dgRelativeKFlatModuleInclusion R D ≫
        (dgNerve.map (Morita.kernelTensor R D E P) ≫
          dgNerve.map (Morita.kernelTensor R E F Q)) := by
  rw [Category.assoc, dgRelativeKFlatKernelNerve_inclusion, ← Category.assoc,
    dgRelativeKFlatKernelNerve_inclusion, Category.assoc]
variable {P P' : BimoduleCategory R E D} {Q Q' : BimoduleCategory R F E}
local notation "P₀" => BimoduleCategory.underlying R E D P
local notation "P₁" => BimoduleCategory.underlying R E D P'
local notation "Q₀" => BimoduleCategory.underlying R F E Q
local notation "Q₁" => BimoduleCategory.underlying R F E Q'
/-- 元の K-flat 指定合成比較は、同じ二つの双加群同型の作用に自然。 -/
lemma dgRelativeKFlatKernelCompositionIso_naturality (f : P ≅ P') (g : Q ≅ Q')
    (hP : Bimodule.rightRelativeKFlat R E D P₀) (hP' : Bimodule.rightRelativeKFlat R E D P₁)
    (hQ : Bimodule.rightRelativeKFlat R F E Q₀) (hQ' : Bimodule.rightRelativeKFlat R F E Q₁) :
    dgRelativeKFlatKernelCompositionIso R D E F P₀ Q₀ hP hQ ≪≫
      dgRelativeKFlatKernelBimoduleIso R D F
        (dgKernelBimoduleComposeIso R D E F f g)
        (Bimodule.rightRelativeKFlat_compose R F E D Q₀ P₀ hQ hP)
        (Bimodule.rightRelativeKFlat_compose R F E D Q₁ P₁ hQ' hP') =
    (dgRelativeKFlatKernelBimoduleIso R D E f hP hP').postcomp
        (dgRelativeKFlatKernelNerve R E F Q₀ hQ) ≪≫
      (dgRelativeKFlatKernelBimoduleIso R E F g hQ hQ').precomp
        (dgRelativeKFlatKernelNerve R D E P₁ hP') ≪≫
      dgRelativeKFlatKernelCompositionIso R D E F P₁ Q₁ hP' hQ' := by
  have hf := pair_inclusion R D E F P₀ Q₀ hP hQ
  have hg := dgRelativeKFlatKernelNerve_inclusion R D F (BimoduleTensor.compose R F E D Q₀ P₀)
    (Bimodule.rightRelativeKFlat_compose R F E D Q₀ P₀ hQ hP)
  have hh := pair_inclusion R D E F P₁ Q₀ hP' hQ
  have ht := pair_inclusion R D E F P₁ Q₁ hP' hQ'
  have hk := dgRelativeKFlatKernelNerve_inclusion R D F (BimoduleTensor.compose R F E D Q₁ P₁)
    (Bimodule.rightRelativeKFlat_compose R F E D Q₁ P₁ hQ' hP')
  have he := congrArg (fun e => FunctorIso.precomp e (dgRelativeKFlatModuleInclusion R D))
    (dgKernelTensorCompositionNerveIso_naturality R D E F f g)
  simp only [F2.functorIso_precomp_trans] at he
  exact functorIso_two_three_reflect_postcomp (dgRelativeKFlatModuleInclusion R F)
    (isFullyFaithful_fullSubcomplexOnVertices_ι (dgModuleNerve R F)
      (dgModuleRelativeKFlatVertex R F)) _ _ _ _ _ _ _ _ _ _ hf hg hh ht hk
    (dgRelativeKFlatKernelCompositionIso_inclusion_heq R D E F P₀ Q₀ hP hQ)
    (dgRelativeKFlatKernelBimoduleIso_inclusion_heq R D F
      (dgKernelBimoduleComposeIso R D E F f g)
      (Bimodule.rightRelativeKFlat_compose R F E D Q₀ P₀ hQ hP)
      (Bimodule.rightRelativeKFlat_compose R F E D Q₁ P₁ hQ' hP'))
    (dgRelativeKFlatKernelBimoduleIso_postcomp_inclusion_heq R D E F f hP hP' Q₀ hQ)
    (dgRelativeKFlatKernelBimoduleIso_precomp_inclusion_heq R D E F g hQ hQ' P₁ hP')
    (dgRelativeKFlatKernelCompositionIso_inclusion_heq R D E F P₁ Q₁ hP' hQ') he
end
end SerrePositivity.InfinityCategories
