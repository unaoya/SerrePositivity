module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCompositionNerveHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGBimoduleAssociatorPrecomp
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCoherencePathTools
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomWhiskerHEq
/-!
概要：元の通常 kernel 合成比較の前後合成を、同じ双加群五角の二辺へ同定する。
方針：元の全関手射・厳密変換・全円柱を保って、端点等式を輸送する。
規約：指定比較を変更しない。使われ方：通常 kernel の五角経路全体の等式。
-/
@[expose] public section
open CategoryTheory
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded SSet MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E F G : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R F] [Small.{u} F] [_root_.SerrePositivity.DifferentialGraded.DGCategory R G] [Small.{u} G]
private lemma source_eq (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R F E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E F Q) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (BimoduleTensor.compose R F E (RightModule R D) Q
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R E D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) P
        (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D)))).toFunctor := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Morita.kernelTensorComposition_eq]
/-- 元の通常合成比較の後合成は、同じ composeMap の実像を保つ。 -/
lemma dgKernelAlpha_postcomp_hom_heq
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R F E) (S : _root_.SerrePositivity.DifferentialGraded.Bimodule R G F) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E F P Q).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R F G S))).hom
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R G (RightModule R D)).map
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R G F (_root_.SerrePositivity.DifferentialGraded.RightModule R D)
          (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R G F S))
          (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R F E D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) Q P
            (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D))).inv)) := by
  have ha := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso_hom_heq R D E F P Q
  have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_postcomp_hom_heq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E F P Q) _ (source_eq R D E F P Q) rfl ha
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R F G S))
  have hm := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensor_postcomp_nerve_hom_heq R F G (RightModule R D)
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R F E D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) Q P
      (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D))).inv (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R G F S)
  exact hh.trans hm.symm
/-- 元の通常合成比較の前合成は、同じ逆結合子の実像を保つ。 -/
lemma dgKernelAlpha_precomp_hom_heq
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R F E) (S : _root_.SerrePositivity.DifferentialGraded.Bimodule R G F) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R E F G Q S).precomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P))).hom
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R G (RightModule R D)).map
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E (_root_.SerrePositivity.DifferentialGraded.RightModule R D) S Q
          (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R E D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) P
            (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D)))).inv) := by
  have ha := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso_hom_heq R E F G Q S
  have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_hom_heq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R E F G Q S) _ (source_eq R E F G Q S) rfl ha
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P))
  have hm := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleAssociator_precomp_nerve_inv_heq R E F
    (_root_.SerrePositivity.DifferentialGraded.RightModule R E) (_root_.SerrePositivity.DifferentialGraded.RightModule R D) G (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D E P) S Q
    (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_comp_identity] at hm
  exact hh.trans hm.symm
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
