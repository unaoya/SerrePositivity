module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FunctorComparisons.DGKernelCompositionNerveNaturality
/-!
概要：元の通常合成比較 α の二変数自然性を、同じ全関手同型の等式へ昇格する。
方針：元の合成双関手の同型像とその射を保ち、全関手射としての自然性を回収する。
規約：指定値を変更しない。使われ方：K-flat と元の導来合成子の自然性。
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
variable {P P' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} {Q Q' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R F E}
local notation "P₀" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P
local notation "P₁" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P'
local notation "Q₀" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q
local notation "Q₁" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q'
/-- 元の二変数の合成双関手で、同じ二つの双加群同型を写す。 -/
def dgKernelBimoduleComposeIso (f : P ≅ P') (g : Q ≅ Q') :=
  (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeFunctor R F E D).mapIso (Iso.prod g f)
omit [Small.{u} D] in
/-- 元の合成双関手で写した同型の射は、同じ composeMap。 -/
lemma dgKernelBimoduleComposeIso_hom (f : P ≅ P') (g : Q ≅ Q') :
    (dgKernelBimoduleComposeIso R D E F f g).hom =
      _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R F E D g.hom f.hom := rfl
/-- 元の通常合成比較 α は、同じ二つの双加群同型の作用に自然。 -/
lemma dgKernelTensorCompositionNerveIso_naturality (f : P ≅ P') (g : Q ≅ Q') :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E F P₀ Q₀ ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso R D F
        (dgKernelBimoduleComposeIso R D E F f g) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso R D E f).postcomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E F Q₀)) ≪≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso R E F g).precomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P₁)) ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E F P₁ Q₁ := by
  apply Iso.ext
  simp only [Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_hom, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_hom,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor_mapIso, CategoryTheory.Functor.mapIso_hom,
    dgKernelBimoduleComposeIso_hom]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso_naturality_hom R D E F f.hom g.hom
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
