module
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelBimoduleIso
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoLiftedWhiskerSquare
/-!
概要：同じ K-flat 双加群同型の前後合成を、包含後に元の通常作用へ戻す。
方針：実可換正方形と同じ指定同型の回収式を保って輸送する。
規約：原 Hom の平坦性を追加しない。使われ方：K-flat 指定合成子の自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E F : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R F] [Small.{u} F]
/-- 同じ K-flat 双加群同型の後合成は、包含後に元の通常作用を回収する。 -/
lemma dgRelativeKFlatKernelBimoduleIso_postcomp_inclusion_heq
    {P P' : BimoduleCategory R E D} (e : P ≅ P')
    (hP : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D P))
    (hP' : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D P'))
    (Q : Bimodule R F E) (hQ : Bimodule.rightRelativeKFlat R F E Q) :
    HEq (((dgRelativeKFlatKernelBimoduleIso R D E e hP hP').postcomp
      (dgRelativeKFlatKernelNerve R E F Q hQ)).postcomp (dgRelativeKFlatModuleInclusion R F))
      (((dgKernelTensorIsoNerveOfBimoduleIso R D E e).postcomp
        (dgNerve.map (Morita.kernelTensor R E F Q))).precomp
          (dgRelativeKFlatModuleInclusion R D)) := by
  exact functorIso_lifted_postcomp_square (dgRelativeKFlatKernelBimoduleIso R D E e hP hP')
    (dgKernelTensorIsoNerveOfBimoduleIso R D E e)
    (dgRelativeKFlatModuleInclusion R D) (dgRelativeKFlatModuleInclusion R E)
    (dgRelativeKFlatKernelNerve R E F Q hQ) (dgRelativeKFlatModuleInclusion R F)
    (dgNerve.map (Morita.kernelTensor R E F Q))
    (dgRelativeKFlatKernelNerve_inclusion R D E (BimoduleCategory.underlying R E D P) hP).symm
    (dgRelativeKFlatKernelNerve_inclusion R D E (BimoduleCategory.underlying R E D P') hP').symm
    (dgRelativeKFlatKernelBimoduleIso_inclusion_heq R D E e hP hP')
    (dgRelativeKFlatKernelNerve_inclusion R E F Q hQ)
/-- 同じ K-flat 双加群同型の前合成は、包含後に元の通常作用を回収する。 -/
lemma dgRelativeKFlatKernelBimoduleIso_precomp_inclusion_heq
    {Q Q' : BimoduleCategory R F E} (e : Q ≅ Q')
    (hQ : Bimodule.rightRelativeKFlat R F E (BimoduleCategory.underlying R F E Q))
    (hQ' : Bimodule.rightRelativeKFlat R F E (BimoduleCategory.underlying R F E Q'))
    (P : Bimodule R E D) (hP : Bimodule.rightRelativeKFlat R E D P) :
    HEq (((dgRelativeKFlatKernelBimoduleIso R E F e hQ hQ').precomp
      (dgRelativeKFlatKernelNerve R D E P hP)).postcomp (dgRelativeKFlatModuleInclusion R F))
      (((dgKernelTensorIsoNerveOfBimoduleIso R E F e).precomp
        (dgNerve.map (Morita.kernelTensor R D E P))).precomp
          (dgRelativeKFlatModuleInclusion R D)) := by
  exact functorIso_lifted_precomp_square (dgRelativeKFlatKernelBimoduleIso R E F e hQ hQ')
    (dgKernelTensorIsoNerveOfBimoduleIso R E F e)
    (dgRelativeKFlatModuleInclusion R E) (dgRelativeKFlatModuleInclusion R F)
    (dgRelativeKFlatKernelNerve R D E P hP) (dgNerve.map (Morita.kernelTensor R D E P))
    (dgRelativeKFlatModuleInclusion R D)
    (dgRelativeKFlatKernelNerve_inclusion R E F (BimoduleCategory.underlying R F E Q) hQ).symm
    (dgRelativeKFlatKernelNerve_inclusion R E F (BimoduleCategory.underlying R F E Q') hQ').symm
    (dgRelativeKFlatKernelBimoduleIso_inclusion_heq R E F e hQ hQ')
    (dgRelativeKFlatKernelNerve_inclusion R D E P hP)
end
end SerrePositivity.InfinityCategories
