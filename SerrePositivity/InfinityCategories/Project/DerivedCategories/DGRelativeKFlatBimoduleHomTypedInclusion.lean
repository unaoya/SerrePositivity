module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomTypedMapBridges
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatKernelBimoduleHom
/-!
概要：包含後の射と自然性の等式を、明示端点の全関手射で照合する。
方針：元の射の像を一般の前後合成で保持する。
規約：可逆性は追加しない。使われ方：K-flat 合成比較の全射自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
lemma dgRelativeKFlatKernelBimoduleHom_typed_inclusion_heq
    {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (f : P ⟶ Q)
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P))
    (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D Q)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D P) hP)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D Q) hQ)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleHom R D E f hP hQ))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D P)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D Q)))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R D E).map f)) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_map_heq _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleHom R D E f hP hQ)).trans
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleHom_inclusion_heq R D E f hP hQ).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_map_heq _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorFunctorHomFunctor R D E).map f)).symm)
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
