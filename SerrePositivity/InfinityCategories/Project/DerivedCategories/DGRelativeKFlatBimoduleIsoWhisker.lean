module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatKernelBimoduleIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoLiftedWhiskerSquare
/-!
概要：同じ K-flat 双加群同型の前後合成を、包含後に元の通常作用へ戻す。
方針：実可換正方形と同じ指定同型の回収式を保って輸送する。
規約：原 Hom の平坦性を追加しない。使われ方：K-flat 指定合成子の自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E F : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R F] [Small.{u} F]
/-- 同じ K-flat 双加群同型の後合成は、包含後に元の通常作用を回収する。 -/
lemma dgRelativeKFlatKernelBimoduleIso_postcomp_inclusion_heq
    {P P' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (e : P ≅ P')
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P))
    (hP' : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P'))
    (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R F E) (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R F E Q) :
    HEq (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleIso R D E e hP hP').postcomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R E F Q hQ)).postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R F))
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso R D E e).postcomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E F Q))).precomp
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D)) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_lifted_postcomp_square (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleIso R D E e hP hP')
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso R D E e)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R E F Q hQ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E F Q))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion R D E (BimoduleCategory.underlying R E D P) hP).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion R D E (BimoduleCategory.underlying R E D P') hP').symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleIso_inclusion_heq R D E e hP hP')
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion R E F Q hQ)
/-- 同じ K-flat 双加群同型の前合成は、包含後に元の通常作用を回収する。 -/
lemma dgRelativeKFlatKernelBimoduleIso_precomp_inclusion_heq
    {Q Q' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R F E} (e : Q ≅ Q')
    (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R F E (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q))
    (hQ' : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R F E (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q'))
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P) :
    HEq (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleIso R E F e hQ hQ').precomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P hP)).postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R F))
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso R E F e).precomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P))).precomp
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D)) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_lifted_precomp_square (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleIso R E F e hQ hQ')
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso R E F e)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P hP) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion R E F (BimoduleCategory.underlying R F E Q) hQ).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion R E F (BimoduleCategory.underlying R F E Q') hQ').symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleIso_inclusion_heq R E F e hQ hQ')
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion R D E P hP)
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
