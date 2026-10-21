module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomLiftedWhiskerSquare
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelBimoduleHom
/-!
概要：K-flat 双加群射の前後合成を、実包含後に元の通常作用へ戻す。
方針：同じ全関手射の指定値と全端点の異種等式を保つ。
規約：可逆性は不要。使われ方：K-flat 合成比較と κ の全射自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E F : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R F] [Small.{u} F]
lemma dgRelativeKFlatKernelBimoduleHom_postcomp_inclusion_heq
    {P P' : BimoduleCategory R E D} (e : P ⟶ P')
    (hP : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D P))
    (hP' : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D P'))
    (Q : Bimodule R F E) (hQ : Bimodule.rightRelativeKFlat R F E Q) :
    HEq ((SSet.mapHomotopyCategory ((ihom (dgRelativeKFlatModuleNerve R D)).map
      (dgRelativeKFlatModuleInclusion R F))).map
        ((SSet.mapHomotopyCategory ((ihom (dgRelativeKFlatModuleNerve R D)).map
          (dgRelativeKFlatKernelNerve R E F Q hQ))).map
            (dgRelativeKFlatKernelBimoduleHom R D E e hP hP')))
      ((SSet.mapHomotopyCategory ((pre (dgRelativeKFlatModuleInclusion R D)).app
        (dgModuleNerve R F))).map
          ((SSet.mapHomotopyCategory ((ihom (dgModuleNerve R D)).map
            (dgNerve.map (Morita.kernelTensor R E F Q)))).map
              ((dgKernelTensorFunctorHomFunctor R D E).map e))) := by
  exact functorHom_lifted_postcomp_square (dgRelativeKFlatKernelBimoduleHom R D E e hP hP')
    ((dgKernelTensorFunctorHomFunctor R D E).map e)
    (dgRelativeKFlatModuleInclusion R D) (dgRelativeKFlatModuleInclusion R E)
    (dgRelativeKFlatKernelNerve R E F Q hQ) (dgRelativeKFlatModuleInclusion R F)
    (dgNerve.map (Morita.kernelTensor R E F Q))
    (dgRelativeKFlatKernelNerve_inclusion R D E (BimoduleCategory.underlying R E D P) hP).symm
    (dgRelativeKFlatKernelNerve_inclusion R D E (BimoduleCategory.underlying R E D P') hP').symm
    (dgRelativeKFlatKernelBimoduleHom_inclusion_heq R D E e hP hP')
    (dgRelativeKFlatKernelNerve_inclusion R E F Q hQ)
lemma dgRelativeKFlatKernelBimoduleHom_precomp_inclusion_heq
    {Q Q' : BimoduleCategory R F E} (e : Q ⟶ Q')
    (hQ : Bimodule.rightRelativeKFlat R F E (BimoduleCategory.underlying R F E Q))
    (hQ' : Bimodule.rightRelativeKFlat R F E (BimoduleCategory.underlying R F E Q'))
    (P : Bimodule R E D) (hP : Bimodule.rightRelativeKFlat R E D P) :
    HEq ((SSet.mapHomotopyCategory ((ihom (dgRelativeKFlatModuleNerve R D)).map
      (dgRelativeKFlatModuleInclusion R F))).map
        ((SSet.mapHomotopyCategory ((pre (dgRelativeKFlatKernelNerve R D E P hP)).app
          (dgRelativeKFlatModuleNerve R F))).map
            (dgRelativeKFlatKernelBimoduleHom R E F e hQ hQ')))
      ((SSet.mapHomotopyCategory ((pre (dgRelativeKFlatModuleInclusion R D)).app
        (dgModuleNerve R F))).map
          ((SSet.mapHomotopyCategory ((pre (dgNerve.map (Morita.kernelTensor R D E P))).app
            (dgModuleNerve R F))).map
              ((dgKernelTensorFunctorHomFunctor R E F).map e))) := by
  exact functorHom_lifted_precomp_square (dgRelativeKFlatKernelBimoduleHom R E F e hQ hQ')
    ((dgKernelTensorFunctorHomFunctor R E F).map e)
    (dgRelativeKFlatModuleInclusion R E) (dgRelativeKFlatModuleInclusion R F)
    (dgRelativeKFlatKernelNerve R D E P hP) (dgNerve.map (Morita.kernelTensor R D E P))
    (dgRelativeKFlatModuleInclusion R D)
    (dgRelativeKFlatKernelNerve_inclusion R E F (BimoduleCategory.underlying R F E Q) hQ).symm
    (dgRelativeKFlatKernelNerve_inclusion R E F (BimoduleCategory.underlying R F E Q') hQ').symm
    (dgRelativeKFlatKernelBimoduleHom_inclusion_heq R E F e hQ hQ')
    (dgRelativeKFlatKernelNerve_inclusion R D E P hP)
end
end SerrePositivity.InfinityCategories
