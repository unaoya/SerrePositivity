module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomLiftedWhiskerSquare
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGRelativeKFlatKernelBimoduleHom
/-!
概要：K-flat 双加群射の前後合成を、実包含後に元の通常作用へ戻す。
方針：同じ全関手射の指定値と全端点の異種等式を保つ。
規約：可逆性は不要。使われ方：K-flat 合成比較と κ の全射自然性。
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
lemma dgRelativeKFlatKernelBimoduleHom_postcomp_inclusion_heq
    {P P' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (e : P ⟶ P')
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P))
    (hP' : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P'))
    (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R F E) (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R F E Q) :
    HEq ((SSet.mapHomotopyCategory ((ihom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleNerve R D)).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R F))).map
        ((SSet.mapHomotopyCategory ((ihom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleNerve R D)).map
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R E F Q hQ))).map
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleHom R D E e hP hP')))
      ((SSet.mapHomotopyCategory ((pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D)).app
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R F))).map
          ((SSet.mapHomotopyCategory ((ihom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R D)).map
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E F Q)))).map
              ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R D E).map e))) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_lifted_postcomp_square (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleHom R D E e hP hP')
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R D E).map e)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R E F Q hQ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E F Q))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion R D E (BimoduleCategory.underlying R E D P) hP).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion R D E (BimoduleCategory.underlying R E D P') hP').symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleHom_inclusion_heq R D E e hP hP')
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion R E F Q hQ)
lemma dgRelativeKFlatKernelBimoduleHom_precomp_inclusion_heq
    {Q Q' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R F E} (e : Q ⟶ Q')
    (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R F E (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q))
    (hQ' : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R F E (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q'))
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P) :
    HEq ((SSet.mapHomotopyCategory ((ihom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleNerve R D)).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R F))).map
        ((SSet.mapHomotopyCategory ((pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P hP)).app
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleNerve R F))).map
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleHom R E F e hQ hQ')))
      ((SSet.mapHomotopyCategory ((pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D)).app
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R F))).map
          ((SSet.mapHomotopyCategory ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P))).app
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R F))).map
              ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R E F).map e))) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_lifted_precomp_square (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleHom R E F e hQ hQ')
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R E F).map e)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P hP) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion R E F (BimoduleCategory.underlying R F E Q) hQ).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion R E F (BimoduleCategory.underlying R F E Q') hQ').symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleHom_inclusion_heq R E F e hQ hQ')
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion R D E P hP)
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
