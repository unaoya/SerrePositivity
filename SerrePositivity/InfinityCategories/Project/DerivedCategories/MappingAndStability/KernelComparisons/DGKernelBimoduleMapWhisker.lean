module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGKernelTensorIsoNerveAlgebra
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelBimoduleMapPrecomp
/-!
概要：元の kernel 射の実全関手射とその前後合成を、同じ composeMap の像へ戻す。
方針：実厳密変換と全 nerve 変換の同じ入力・出力作用を保つ。
規約：原 Hom の平坦性を追加しない。使われ方：指定合成子 α の自然性。
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
/-- 元の通常 kernel 射の全関手射は、同じ composeMap の実像。 -/
lemma dgKernelTensorFunctorHomFunctor_map {P P' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (f : P ⟶ P') :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R D E).map f =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R E (RightModule R D)).map
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R E D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) f
          (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D))))) := rfl
/-- 元の kernel 射の通常後合成は、同じ composeMap の全関手射。 -/
lemma dgKernelTensorFunctorHomFunctor_postcomp_heq {P P' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D}
    (f : P ⟶ P') (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R F E) :
    HEq ((SSet.mapHomotopyCategory ((ihom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R D)).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E F Q)))).map
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R D E).map f))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R F (RightModule R D)).map
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R F E (_root_.SerrePositivity.DifferentialGraded.RightModule R D)
          (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R F E Q))
          (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R E D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) f
            (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R D (_root_.SerrePositivity.DifferentialGraded.RightModule R D)
              (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D))))))) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensor_postcomp_nerve_hom_heq R E F (RightModule R D)
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R E D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) f
      (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D)))))
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R F E Q)).symm
/-- 元の kernel 射の通常前合成は、同じ composeMap の全関手射。 -/
lemma dgKernelTensorFunctorHomFunctor_precomp_heq {Q Q' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R F E}
    (g : Q ⟶ Q') (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    HEq ((SSet.mapHomotopyCategory ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P))).app
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R F))).map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R E F).map g))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R F (RightModule R D)).map
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R F E (_root_.SerrePositivity.DifferentialGraded.RightModule R D) g
          (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D E P))))) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelBimoduleMap_precomp_nerve_hom_heq R E F (RightModule R D) g
    (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D E P)).symm
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
