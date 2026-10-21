module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomTypedMapBridges
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatBimoduleHomWhisker
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelBimoduleHom
/-!
概要：K-flat 双加群射の前後合成を、同じ型付きの包含後の像へ照合する。
方針：実包含後の回収式と前後合成の異種等式を使う。
規約：可逆性は不要。使われ方：K-flat 指定合成比較の全射自然性。
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
lemma dgRelativeKFlatKernelBimoduleHom_typed_postcomp_inclusion_heq
    {P P' : BimoduleCategory R E D} (e : P ⟶ P')
    (hP : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D P))
    (hP' : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D P'))
    (Q : Bimodule R F E) (hQ : Bimodule.rightRelativeKFlat R F E Q) :
    HEq (functorHomPostcomp
      (dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D P) hP ≫
        dgRelativeKFlatKernelNerve R E F Q hQ)
      (dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D P') hP' ≫
        dgRelativeKFlatKernelNerve R E F Q hQ)
      (dgRelativeKFlatModuleInclusion R F)
      (functorHomPostcomp
        (dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D P) hP)
        (dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D P') hP')
        (dgRelativeKFlatKernelNerve R E F Q hQ)
        (dgRelativeKFlatKernelBimoduleHom R D E e hP hP')))
      (functorHomPrecomp
        (dgNerve.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D P)) ≫
          dgNerve.map (Morita.kernelTensor R E F Q))
        (dgNerve.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D P')) ≫
          dgNerve.map (Morita.kernelTensor R E F Q))
        (dgRelativeKFlatModuleInclusion R D)
        (functorHomPostcomp
          (dgNerve.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D P)))
          (dgNerve.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D P')))
          (dgNerve.map (Morita.kernelTensor R E F Q))
          ((dgKernelTensorFunctorHomFunctor R D E).map e))) := by
  exact (functorHomPostcomp_postcomp_map_heq _ _ _ _
    (dgRelativeKFlatKernelBimoduleHom R D E e hP hP')).trans
    ((dgRelativeKFlatKernelBimoduleHom_postcomp_inclusion_heq R D E F e hP hP' Q hQ).trans
      (functorHomPostcomp_precomp_map_heq _ _ _ _
        ((dgKernelTensorFunctorHomFunctor R D E).map e)).symm)
lemma dgRelativeKFlatKernelBimoduleHom_typed_precomp_inclusion_heq
    {Q Q' : BimoduleCategory R F E} (e : Q ⟶ Q')
    (hQ : Bimodule.rightRelativeKFlat R F E (BimoduleCategory.underlying R F E Q))
    (hQ' : Bimodule.rightRelativeKFlat R F E (BimoduleCategory.underlying R F E Q'))
    (P : Bimodule R E D) (hP : Bimodule.rightRelativeKFlat R E D P) :
    HEq (functorHomPostcomp
      (dgRelativeKFlatKernelNerve R D E P hP ≫ dgRelativeKFlatKernelNerve R E F
        (BimoduleCategory.underlying R F E Q) hQ)
      (dgRelativeKFlatKernelNerve R D E P hP ≫ dgRelativeKFlatKernelNerve R E F
        (BimoduleCategory.underlying R F E Q') hQ')
      (dgRelativeKFlatModuleInclusion R F)
      (functorHomPrecomp
        (dgRelativeKFlatKernelNerve R E F (BimoduleCategory.underlying R F E Q) hQ)
        (dgRelativeKFlatKernelNerve R E F (BimoduleCategory.underlying R F E Q') hQ')
        (dgRelativeKFlatKernelNerve R D E P hP)
        (dgRelativeKFlatKernelBimoduleHom R E F e hQ hQ')))
      (functorHomPrecomp
        (dgNerve.map (Morita.kernelTensor R D E P) ≫ dgNerve.map
          (Morita.kernelTensor R E F (BimoduleCategory.underlying R F E Q)))
        (dgNerve.map (Morita.kernelTensor R D E P) ≫ dgNerve.map
          (Morita.kernelTensor R E F (BimoduleCategory.underlying R F E Q')))
        (dgRelativeKFlatModuleInclusion R D)
        (functorHomPrecomp
          (dgNerve.map (Morita.kernelTensor R E F (BimoduleCategory.underlying R F E Q)))
          (dgNerve.map (Morita.kernelTensor R E F (BimoduleCategory.underlying R F E Q')))
          (dgNerve.map (Morita.kernelTensor R D E P))
          ((dgKernelTensorFunctorHomFunctor R E F).map e))) := by
  exact (functorHomPrecomp_postcomp_map_heq _ _ _ _
    (dgRelativeKFlatKernelBimoduleHom R E F e hQ hQ')).trans
    ((dgRelativeKFlatKernelBimoduleHom_precomp_inclusion_heq R D E F e hQ hQ' P hP).trans
      (functorHomPrecomp_precomp_map_heq _ _ _ _
        ((dgKernelTensorFunctorHomFunctor R E F).map e)).symm)
end
end SerrePositivity.InfinityCategories
