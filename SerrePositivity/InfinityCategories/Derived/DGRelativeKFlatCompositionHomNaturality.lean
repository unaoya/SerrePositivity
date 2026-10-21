module
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatBimoduleHomTypedInclusion
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatBimoduleHomTypedWhisker
public import SerrePositivity.InfinityCategories.Derived.FunctorHomTypedWhiskerEquation
public import SerrePositivity.InfinityCategories.Derived.FunctorHomTypedPathReflection
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoLiftedTypedHom
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoLiftedHom
public import SerrePositivity.InfinityCategories.Derived.DGKernelCompositionNerveNaturality
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatBimoduleHomWhisker
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatCompatibilityInclusion
public import SerrePositivity.InfinityCategories.Derived.FunctorHomLiftedPathReflection
public import SerrePositivity.InfinityCategories.Derived.FunctorHomSquareTransport
public import SerrePositivity.InfinityCategories.Derived.FunctorHomWhiskering
/-!
概要：元の K-flat 指定合成比較の任意双加群射に対する二変数自然性を証明する。
方針：同じ指定比較と射の値を保持し、全関手圏の等式を照合する。
規約：可逆性は追加しない。使われ方：元の κ の全射自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
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
lemma dgRelativeKFlatKernelCompositionIso_naturality_hom
    (f : P ⟶ P') (g : Q ⟶ Q')
    (hP : Bimodule.rightRelativeKFlat R E D P₀) (hP' : Bimodule.rightRelativeKFlat R E D P₁)
    (hQ : Bimodule.rightRelativeKFlat R F E Q₀) (hQ' : Bimodule.rightRelativeKFlat R F E Q₁) :
    (dgRelativeKFlatKernelCompositionIso R D E F P₀ Q₀ hP hQ).hom ≫
      dgRelativeKFlatKernelBimoduleHom R D F (BimoduleTensor.composeMap R F E D g f)
        (Bimodule.rightRelativeKFlat_compose R F E D Q₀ P₀ hQ hP)
        (Bimodule.rightRelativeKFlat_compose R F E D Q₁ P₁ hQ' hP') =
    functorHomPostcomp
      (dgRelativeKFlatKernelNerve R D E P₀ hP) (dgRelativeKFlatKernelNerve R D E P₁ hP')
      (dgRelativeKFlatKernelNerve R E F Q₀ hQ)
      (dgRelativeKFlatKernelBimoduleHom R D E f hP hP') ≫
    functorHomPrecomp
      (dgRelativeKFlatKernelNerve R E F Q₀ hQ) (dgRelativeKFlatKernelNerve R E F Q₁ hQ')
      (dgRelativeKFlatKernelNerve R D E P₁ hP')
      (dgRelativeKFlatKernelBimoduleHom R E F g hQ hQ') ≫
      (dgRelativeKFlatKernelCompositionIso R D E F P₁ Q₁ hP' hQ').hom := by
  have hf := pair_inclusion R D E F P₀ Q₀ hP hQ
  have hg := dgRelativeKFlatKernelNerve_inclusion R D F (BimoduleTensor.compose R F E D Q₀ P₀)
    (Bimodule.rightRelativeKFlat_compose R F E D Q₀ P₀ hQ hP)
  have hh := pair_inclusion R D E F P₁ Q₀ hP' hQ
  have ht := pair_inclusion R D E F P₁ Q₁ hP' hQ'
  have hk := dgRelativeKFlatKernelNerve_inclusion R D F (BimoduleTensor.compose R F E D Q₁ P₁)
    (Bimodule.rightRelativeKFlat_compose R F E D Q₁ P₁ hQ' hP')
  have hc := functorIso_lifted_typed_hom_heq
    (dgRelativeKFlatKernelCompositionIso R D E F P₀ Q₀ hP hQ)
    (dgKernelTensorCompositionNerveIso R D E F P₀ Q₀)
    (dgRelativeKFlatModuleInclusion R D) (dgRelativeKFlatModuleInclusion R F) hf hg
    (dgRelativeKFlatKernelCompositionIso_inclusion_heq R D E F P₀ Q₀ hP hQ)
  have ha := functorIso_lifted_typed_hom_heq
    (dgRelativeKFlatKernelCompositionIso R D E F P₁ Q₁ hP' hQ')
    (dgKernelTensorCompositionNerveIso R D E F P₁ Q₁)
    (dgRelativeKFlatModuleInclusion R D) (dgRelativeKFlatModuleInclusion R F) ht hk
    (dgRelativeKFlatKernelCompositionIso_inclusion_heq R D E F P₁ Q₁ hP' hQ')
  let p₀ := dgRelativeKFlatKernelNerve R D E P₀ hP
  let p₁ := dgRelativeKFlatKernelNerve R D E P₁ hP'
  let q₀ := dgRelativeKFlatKernelNerve R E F Q₀ hQ
  let q₁ := dgRelativeKFlatKernelNerve R E F Q₁ hQ'
  let kp₀ := dgNerve.map (Morita.kernelTensor R D E P₀)
  let kp₁ := dgNerve.map (Morita.kernelTensor R D E P₁)
  let kq₀ := dgNerve.map (Morita.kernelTensor R E F Q₀)
  let kq₁ := dgNerve.map (Morita.kernelTensor R E F Q₁)
  let iD := dgRelativeKFlatModuleInclusion R D
  let iF := dgRelativeKFlatModuleInclusion R F
  let gp₀ := dgRelativeKFlatKernelNerve R D F (BimoduleTensor.compose R F E D Q₀ P₀)
    (Bimodule.rightRelativeKFlat_compose R F E D Q₀ P₀ hQ hP)
  let gp₁ := dgRelativeKFlatKernelNerve R D F (BimoduleTensor.compose R F E D Q₁ P₁)
    (Bimodule.rightRelativeKFlat_compose R F E D Q₁ P₁ hQ' hP')
  let kg₀ := dgNerve.map (Morita.kernelTensor R D F (BimoduleTensor.compose R F E D Q₀ P₀))
  let kg₁ := dgNerve.map (Morita.kernelTensor R D F (BimoduleTensor.compose R F E D Q₁ P₁))
  have hr := dgRelativeKFlatKernelBimoduleHom_typed_inclusion_heq R D F
    (BimoduleTensor.composeMap R F E D g f)
    (Bimodule.rightRelativeKFlat_compose R F E D Q₀ P₀ hQ hP)
    (Bimodule.rightRelativeKFlat_compose R F E D Q₁ P₁ hQ' hP')
  have hq := dgRelativeKFlatKernelBimoduleHom_typed_postcomp_inclusion_heq
    R D E F f hP hP' Q₀ hQ
  have hd := dgRelativeKFlatKernelBimoduleHom_typed_precomp_inclusion_heq
    R D E F g hQ hQ' P₁ hP'
  have he := functorHom_two_three_typed_whisker_eq kp₀ kp₁ kq₀ kq₁ kg₀ kg₁
    ((dgKernelTensorFunctorHomFunctor R D E).map f)
    ((dgKernelTensorFunctorHomFunctor R E F).map g)
    (dgKernelTensorCompositionNerveIso R D E F P₀ Q₀).hom
    ((dgKernelTensorFunctorHomFunctor R D F).map (BimoduleTensor.composeMap R F E D g f))
    (dgKernelTensorCompositionNerveIso R D E F P₁ Q₁).hom
    (dgKernelTensorCompositionNerveIso_naturality_hom R D E F f g)
  exact functorHom_two_three_reflect_typed_precomp
    (f := p₀ ≫ q₀) (g := gp₀) (h := p₁ ≫ q₀) (t := p₁ ≫ q₁) (k := gp₁)
    (f' := kp₀ ≫ kq₀) (g' := kg₀) (h' := kp₁ ≫ kq₀) (t' := kp₁ ≫ kq₁) (k' := kg₁)
    iF (isFullyFaithful_fullSubcomplexOnVertices_ι (dgModuleNerve R F)
      (dgModuleRelativeKFlatVertex R F)) iD
    (dgRelativeKFlatKernelCompositionIso R D E F P₀ Q₀ hP hQ).hom
    (dgRelativeKFlatKernelBimoduleHom R D F (BimoduleTensor.composeMap R F E D g f)
      (Bimodule.rightRelativeKFlat_compose R F E D Q₀ P₀ hQ hP)
      (Bimodule.rightRelativeKFlat_compose R F E D Q₁ P₁ hQ' hP'))
    (functorHomPostcomp p₀ p₁ q₀ (dgRelativeKFlatKernelBimoduleHom R D E f hP hP'))
    (functorHomPrecomp q₀ q₁ p₁ (dgRelativeKFlatKernelBimoduleHom R E F g hQ hQ'))
    (dgRelativeKFlatKernelCompositionIso R D E F P₁ Q₁ hP' hQ').hom
    (dgKernelTensorCompositionNerveIso R D E F P₀ Q₀).hom
    ((dgKernelTensorFunctorHomFunctor R D F).map (BimoduleTensor.composeMap R F E D g f))
    (functorHomPostcomp kp₀ kp₁ kq₀ ((dgKernelTensorFunctorHomFunctor R D E).map f))
    (functorHomPrecomp kq₀ kq₁ kp₁ ((dgKernelTensorFunctorHomFunctor R E F).map g))
    (dgKernelTensorCompositionNerveIso R D E F P₁ Q₁).hom
    hf hg hh ht hk hc hr hq hd ha he
end
end SerrePositivity.InfinityCategories
