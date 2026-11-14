module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FunctorComparisons.DGKernelCompositionNerveNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomPostcompIdentityMap
/-!
概要：元の kernel 合成子の右変数自然性を、同じ通常比較と raw 経路で照合する。
方針：元の指定比較と射の値を保持し、全関手圏の実作用と可換四角形を使う。
規約：後続 kernel の平坦性・射の可逆性は要求しない。使われ方：模型変更の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
variable (R : Type u) [CommRing R] (D E K : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R K] [Small.{u} K]
lemma dgKernelTensorCompositionNerveIso_right_naturality
    (P : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D) {Q0 Q1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R K E} (g : Q0 ⟶ Q1) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E K
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P) (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R K E Q0)).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R D K).map
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R K E D g (𝟙 P)) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E K (BimoduleCategory.underlying R K E Q0)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E K (BimoduleCategory.underlying R K E Q1)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D P)))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R E K).map g) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E K
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P) (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R K E Q1)).hom := by
  have hi : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R D E).map (𝟙 P) =
      𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D E (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P))))) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R D E).map_id P
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso_naturality_hom R D E K (𝟙 P) g
  rw [hi] at hn
  have hp : (SSet.mapHomotopyCategory ((ihom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R D)).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E K (BimoduleCategory.underlying R K E Q0))))).map
      (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D E (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P)))))) =
      𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D P)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E K (BimoduleCategory.underlying R K E Q0))))) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_identity _ _
  rw [hp] at hn
  let z : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D P)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E K (BimoduleCategory.underlying R K E Q0)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D K (BimoduleTensor.compose R K E D
        (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R K E Q1) (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P)))) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E K (BimoduleCategory.underlying R K E Q0)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E K (BimoduleCategory.underlying R K E Q1)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D P)))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R E K).map g) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E K
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P) (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R K E Q1)).hom
  exact hn.trans (Category.id_comp z)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
