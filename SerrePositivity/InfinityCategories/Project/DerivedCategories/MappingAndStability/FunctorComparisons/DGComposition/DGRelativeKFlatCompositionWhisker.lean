module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGRelativeKFlatCompatibilityInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorIsoLiftedWhiskerSquare
/-!
概要：K-flat の元の合成比較の前後合成を、包含後に通常比較へ同定する。
方針：実包含の可換正方形と同じ指定比較の異種等式を保つ。
規約：原 Hom の平坦性を追加しない。使われ方：K-flat の五角式の経路反映。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E F G : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R F] [Small.{u} F] [_root_.SerrePositivity.DifferentialGraded.DGCategory R G] [Small.{u} G]
private lemma pair_inclusion (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R F E)
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P) (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R F E Q) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P hP ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R E F Q hQ) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R F =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E F Q)) := by
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion, Category.assoc]
/-- 元の K-flat 合成比較の後合成は、包含後に同じ通常比較を回収する。 -/
lemma dgRelativeKFlatKernelComposition_postcomp_inclusion_heq
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R F E) (S : _root_.SerrePositivity.DifferentialGraded.Bimodule R G F)
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P) (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R F E Q)
    (hS : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R G F S) :
    HEq (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R D E F P Q hP hQ).postcomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R F G S hS)).postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R G))
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E F P Q).postcomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R F G S))).precomp
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D)) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_lifted_postcomp_square
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R D E F P Q hP hQ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E F P Q)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R F G S hS) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R G)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R F G S)) (pair_inclusion R D E F P Q hP hQ).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion R D F (BimoduleTensor.compose R F E D Q P)
      (_root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R F E D Q P hQ hP)).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso_inclusion_heq R D E F P Q hP hQ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion R F G S hS)
/-- 元の K-flat 合成比較の前合成は、包含後に同じ通常比較を回収する。 -/
lemma dgRelativeKFlatKernelComposition_precomp_inclusion_heq
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R F E) (S : _root_.SerrePositivity.DifferentialGraded.Bimodule R G F)
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P) (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R F E Q)
    (hS : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R G F S) :
    HEq (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R E F G Q S hQ hS).precomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P hP)).postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R G))
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R E F G Q S).precomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P))).precomp
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D)) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_lifted_precomp_square
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R E F G Q S hQ hS)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R E F G Q S)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R G)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P hP) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D) (pair_inclusion R E F G Q S hQ hS).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion R E G (BimoduleTensor.compose R G F E S Q)
      (_root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R G F E S Q hS hQ)).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso_inclusion_heq R E F G Q S hQ hS)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion R D E P hP)
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
