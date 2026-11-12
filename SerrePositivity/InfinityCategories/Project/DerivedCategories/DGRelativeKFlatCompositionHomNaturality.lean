module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatBimoduleHomTypedInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatBimoduleHomTypedWhisker
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomTypedWhiskerEquation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomTypedPathReflection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoLiftedTypedHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoLiftedHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCompositionNerveNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatBimoduleHomWhisker
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatCompatibilityInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomLiftedPathReflection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomSquareTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomWhiskering
/-!
概要：元の K-flat 指定合成比較の任意双加群射に対する二変数自然性を証明する。
方針：同じ指定比較と射の値を保持し、全関手圏の等式を照合する。
規約：可逆性は追加しない。使われ方：元の κ の全射自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
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
lemma dgRelativeKFlatKernelCompositionIso_naturality_hom
    (f : P ⟶ P') (g : Q ⟶ Q')
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P₀) (hP' : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P₁)
    (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R F E Q₀) (hQ' : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R F E Q₁) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R D E F P₀ Q₀ hP hQ).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleHom R D F (BimoduleTensor.composeMap R F E D g f)
        (_root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R F E D Q₀ P₀ hQ hP)
        (_root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R F E D Q₁ P₁ hQ' hP') =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P₀ hP) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P₁ hP')
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R E F Q₀ hQ)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleHom R D E f hP hP') ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R E F Q₀ hQ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R E F Q₁ hQ')
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P₁ hP')
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleHom R E F g hQ hQ') ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R D E F P₁ Q₁ hP' hQ').hom := by
  have hf := pair_inclusion R D E F P₀ Q₀ hP hQ
  have hg := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion R D F (BimoduleTensor.compose R F E D Q₀ P₀)
    (_root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R F E D Q₀ P₀ hQ hP)
  have hh := pair_inclusion R D E F P₁ Q₀ hP' hQ
  have ht := pair_inclusion R D E F P₁ Q₁ hP' hQ'
  have hk := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion R D F (BimoduleTensor.compose R F E D Q₁ P₁)
    (_root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R F E D Q₁ P₁ hQ' hP')
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_lifted_typed_hom_heq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R D E F P₀ Q₀ hP hQ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E F P₀ Q₀)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R F) hf hg
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso_inclusion_heq R D E F P₀ Q₀ hP hQ)
  have ha := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_lifted_typed_hom_heq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R D E F P₁ Q₁ hP' hQ')
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E F P₁ Q₁)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R F) ht hk
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso_inclusion_heq R D E F P₁ Q₁ hP' hQ')
  let p₀ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P₀ hP
  let p₁ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P₁ hP'
  let q₀ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R E F Q₀ hQ
  let q₁ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R E F Q₁ hQ'
  let kp₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P₀)
  let kp₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P₁)
  let kq₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E F Q₀)
  let kq₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E F Q₁)
  let iD := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D
  let iF := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R F
  let gp₀ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D F (BimoduleTensor.compose R F E D Q₀ P₀)
    (_root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R F E D Q₀ P₀ hQ hP)
  let gp₁ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D F (BimoduleTensor.compose R F E D Q₁ P₁)
    (_root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R F E D Q₁ P₁ hQ' hP')
  let kg₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D F (BimoduleTensor.compose R F E D Q₀ P₀))
  let kg₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D F (BimoduleTensor.compose R F E D Q₁ P₁))
  have hr := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleHom_typed_inclusion_heq R D F
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R F E D g f)
    (_root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R F E D Q₀ P₀ hQ hP)
    (_root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R F E D Q₁ P₁ hQ' hP')
  have hq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleHom_typed_postcomp_inclusion_heq
    R D E F f hP hP' Q₀ hQ
  have hd := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleHom_typed_precomp_inclusion_heq
    R D E F g hQ hQ' P₁ hP'
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_two_three_typed_whisker_eq kp₀ kp₁ kq₀ kq₁ kg₀ kg₁
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R D E).map f)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R E F).map g)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E F P₀ Q₀).hom
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R D F).map (BimoduleTensor.composeMap R F E D g f))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E F P₁ Q₁).hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso_naturality_hom R D E F f g)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_two_three_reflect_typed_precomp
    (f := p₀ ≫ q₀) (g := gp₀) (h := p₁ ≫ q₀) (t := p₁ ≫ q₁) (k := gp₁)
    (f' := kp₀ ≫ kq₀) (g' := kg₀) (h' := kp₁ ≫ kq₀) (t' := kp₁ ≫ kq₁) (k' := kg₁)
    iF (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R F)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleRelativeKFlatVertex R F)) iD
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R D E F P₀ Q₀ hP hQ).hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleHom R D F (BimoduleTensor.composeMap R F E D g f)
      (_root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R F E D Q₀ P₀ hQ hP)
      (_root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R F E D Q₁ P₁ hQ' hP'))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp p₀ p₁ q₀ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleHom R D E f hP hP'))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp q₀ q₁ p₁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleHom R E F g hQ hQ'))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R D E F P₁ Q₁ hP' hQ').hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E F P₀ Q₀).hom
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R D F).map (BimoduleTensor.composeMap R F E D g f))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp kp₀ kp₁ kq₀ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R D E).map f))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp kq₀ kq₁ kp₁ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R E F).map g))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E F P₁ Q₁).hom
    hf hg hh ht hk hc hr hq hd ha he
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
