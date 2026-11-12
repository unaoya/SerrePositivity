module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelInverseAssociatorNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelBimoduleMapWhisker
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCompositionNerveHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomTwoThreeTransport
/-!
概要：元の通常 kernel 合成比較 α の双加群射に対する二変数自然性を証明する。
方針：同じ逆結合子の自然性と二変数の実作用を、明示した全端点に沿って照合する。
規約：射の可逆性・原 Hom の平坦性を追加しない。使われ方：左単位と模型変更 coherence。
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
private lemma source_eq (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R F E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E F Q) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (BimoduleTensor.compose R F E (RightModule R D) Q
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R E D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) P
        (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D)))).toFunctor := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Morita.kernelTensorComposition_eq]
variable {P P' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} {Q Q' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R F E}
local notation "P₀" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P
local notation "P₁" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P'
local notation "Q₀" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q
local notation "Q₁" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q'
/-- 元の通常合成比較 α は、任意の二つの閉零双加群射に対して全関手射として自然。 -/
lemma dgKernelTensorCompositionNerveIso_naturality_hom (f : P ⟶ P') (g : Q ⟶ Q') :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E F P₀ Q₀).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R D F).map (BimoduleTensor.composeMap R F E D g f) =
    (SSet.mapHomotopyCategory ((ihom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R D)).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E F Q₀)))).map
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R D E).map f) ≫
    (SSet.mapHomotopyCategory ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P₁))).app
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R F))).map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R E F).map g) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E F P₁ Q₁).hom := by
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso_hom_heq R D E F P₀ Q₀
  have hr := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor_map R D F
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R F E D g f))
  have hq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor_postcomp_heq R D E F f Q₀
  have hd := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor_precomp_heq R D E F g P₁
  have ha := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso_hom_heq R D E F P₁ Q₁
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelInverseAssociatorNerve_naturality_factor R D E F f g
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_two_three_eq_of_heq
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P₀) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E F Q₀))
    (g := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D F (BimoduleTensor.compose R F E D Q₀ P₀)))
    (h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P₁) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E F Q₀))
    (t := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P₁) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E F Q₁))
    (k := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D F (BimoduleTensor.compose R F E D Q₁ P₁)))
    _ _ _ _ _ _ _ _ _ _
    (source_eq R D E F P₀ Q₀) rfl (source_eq R D E F P₁ Q₀)
    (source_eq R D E F P₁ Q₁) rfl hc hr hq hd ha he

end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
