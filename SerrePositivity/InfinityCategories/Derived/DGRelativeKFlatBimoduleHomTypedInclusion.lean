module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomTypedMapBridges
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelBimoduleHom
/-!
概要：包含後の射と自然性の等式を、明示端点の全関手射で照合する。
方針：元の射の像を一般の前後合成で保持する。
規約：可逆性は追加しない。使われ方：K-flat 合成比較の全射自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
lemma dgRelativeKFlatKernelBimoduleHom_typed_inclusion_heq
    {P Q : BimoduleCategory R E D} (f : P ⟶ Q)
    (hP : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D P))
    (hQ : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D Q)) :
    HEq (functorHomPostcomp
      (dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D P) hP)
      (dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D Q) hQ)
      (dgRelativeKFlatModuleInclusion R E) (dgRelativeKFlatKernelBimoduleHom R D E f hP hQ))
      (functorHomPrecomp
        (dgNerve.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D P)))
        (dgNerve.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D Q)))
        (dgRelativeKFlatModuleInclusion R D) ((dgKernelTensorFunctorHomFunctor R D E).map f)) := by
  exact (functorHomPostcomp_map_heq _ _ (dgRelativeKFlatModuleInclusion R E)
    (dgRelativeKFlatKernelBimoduleHom R D E f hP hQ)).trans
    ((dgRelativeKFlatKernelBimoduleHom_inclusion_heq R D E f hP hQ).trans
      (functorHomPrecomp_map_heq _ _ (dgRelativeKFlatModuleInclusion R D)
        ((dgKernelTensorFunctorHomFunctor R D E).map f)).symm)
end
end SerrePositivity.InfinityCategories
