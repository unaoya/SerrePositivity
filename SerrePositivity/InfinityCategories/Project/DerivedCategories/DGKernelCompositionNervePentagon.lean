module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCompositionNerveWhisker
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGBimoduleNerveInversePentagon
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelBimoduleIsoNerveHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomTwoThreeTransport
/-!
概要：元の通常 kernel 合成比較の三 kernel 五角経路を、全関手同型として証明する。
方針：同じ双加群逆五角の実像の各辺を、元の指定比較へ端点付きで同定する。
規約：頂点成分一致へ弱めず、原 Hom の平坦性を仮定しない。
使われ方：K-flat の通常比較と元の導来合成子への coherence の移送。
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
/-- 元の通常 kernel の指定合成比較は、同じ双加群結合子と五角経路を満たす。 -/
lemma dgKernelTensorCompositionNerveIso_pentagon
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R F E) (S : _root_.SerrePositivity.DifferentialGraded.Bimodule R G F) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E F P Q).postcomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R F G S)) ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D F G (BimoduleTensor.compose R F E D Q P) S =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R E F G Q S).precomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P)) ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E G P (BimoduleTensor.compose R G F E S Q) ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso R D G
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E D S Q P) := by
  have hf : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E F Q)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R F G S) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (BimoduleTensor.compose R G F (RightModule R D) S
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R F E (_root_.SerrePositivity.DifferentialGraded.RightModule R D) Q
          (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R E D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) P
            (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D))))).toFunctor := by
    rw [source_eq R D E F P Q, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensor_postcomp_bimodule_eq]
  have hg := source_eq R D F G (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R F E D Q P) S
  have hh := source_eq R D E G P (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R G F E S Q)
  apply Iso.ext
  change ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E F P Q).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R F G S))).hom ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D F G (BimoduleTensor.compose R F E D Q P) S).hom =
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R E F G Q S).precomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P))).hom ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E G P (BimoduleTensor.compose R G F E S Q)).hom ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso R D G
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E D S Q P)).hom
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_two_three_eq_of_heq _ _ _ _ _ _ _ _ _ _ hf hg hh rfl rfl
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelAlpha_postcomp_hom_heq R D E F G P Q S)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso_hom_heq R D F G
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R F E D Q P) S)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelAlpha_precomp_hom_heq R D E F G P Q S)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso_hom_heq R D E G P
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R G F E S Q))
    (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso_hom R D G
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E D S Q P)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleNerve_inverse_pentagon_hom R G F E D (RightModule R D) S Q P
      (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D)))
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
