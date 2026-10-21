module
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatCompatibilityInclusion
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoLiftedWhiskerSquare
/-!
概要：K-flat の元の合成比較の前後合成を、包含後に通常比較へ同定する。
方針：実包含の可換正方形と同じ指定比較の異種等式を保つ。
規約：原 Hom の平坦性を追加しない。使われ方：K-flat の五角式の経路反映。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E F G : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R F] [Small.{u} F] [DGCategory R G] [Small.{u} G]
private lemma pair_inclusion (P : Bimodule R E D) (Q : Bimodule R F E)
    (hP : Bimodule.rightRelativeKFlat R E D P) (hQ : Bimodule.rightRelativeKFlat R F E Q) :
    (dgRelativeKFlatKernelNerve R D E P hP ≫ dgRelativeKFlatKernelNerve R E F Q hQ) ≫
      dgRelativeKFlatModuleInclusion R F =
    dgRelativeKFlatModuleInclusion R D ≫
      (dgNerve.map (Morita.kernelTensor R D E P) ≫
        dgNerve.map (Morita.kernelTensor R E F Q)) := by
  rw [Category.assoc, dgRelativeKFlatKernelNerve_inclusion, ← Category.assoc,
    dgRelativeKFlatKernelNerve_inclusion, Category.assoc]
/-- 元の K-flat 合成比較の後合成は、包含後に同じ通常比較を回収する。 -/
lemma dgRelativeKFlatKernelComposition_postcomp_inclusion_heq
    (P : Bimodule R E D) (Q : Bimodule R F E) (S : Bimodule R G F)
    (hP : Bimodule.rightRelativeKFlat R E D P) (hQ : Bimodule.rightRelativeKFlat R F E Q)
    (hS : Bimodule.rightRelativeKFlat R G F S) :
    HEq (((dgRelativeKFlatKernelCompositionIso R D E F P Q hP hQ).postcomp
      (dgRelativeKFlatKernelNerve R F G S hS)).postcomp (dgRelativeKFlatModuleInclusion R G))
      (((dgKernelTensorCompositionNerveIso R D E F P Q).postcomp
        (dgNerve.map (Morita.kernelTensor R F G S))).precomp
          (dgRelativeKFlatModuleInclusion R D)) := by
  exact functorIso_lifted_postcomp_square
    (dgRelativeKFlatKernelCompositionIso R D E F P Q hP hQ)
    (dgKernelTensorCompositionNerveIso R D E F P Q)
    (dgRelativeKFlatModuleInclusion R D) (dgRelativeKFlatModuleInclusion R F)
    (dgRelativeKFlatKernelNerve R F G S hS) (dgRelativeKFlatModuleInclusion R G)
    (dgNerve.map (Morita.kernelTensor R F G S)) (pair_inclusion R D E F P Q hP hQ).symm
    (dgRelativeKFlatKernelNerve_inclusion R D F (BimoduleTensor.compose R F E D Q P)
      (Bimodule.rightRelativeKFlat_compose R F E D Q P hQ hP)).symm
    (dgRelativeKFlatKernelCompositionIso_inclusion_heq R D E F P Q hP hQ)
    (dgRelativeKFlatKernelNerve_inclusion R F G S hS)
/-- 元の K-flat 合成比較の前合成は、包含後に同じ通常比較を回収する。 -/
lemma dgRelativeKFlatKernelComposition_precomp_inclusion_heq
    (P : Bimodule R E D) (Q : Bimodule R F E) (S : Bimodule R G F)
    (hP : Bimodule.rightRelativeKFlat R E D P) (hQ : Bimodule.rightRelativeKFlat R F E Q)
    (hS : Bimodule.rightRelativeKFlat R G F S) :
    HEq (((dgRelativeKFlatKernelCompositionIso R E F G Q S hQ hS).precomp
      (dgRelativeKFlatKernelNerve R D E P hP)).postcomp (dgRelativeKFlatModuleInclusion R G))
      (((dgKernelTensorCompositionNerveIso R E F G Q S).precomp
        (dgNerve.map (Morita.kernelTensor R D E P))).precomp
          (dgRelativeKFlatModuleInclusion R D)) := by
  exact functorIso_lifted_precomp_square
    (dgRelativeKFlatKernelCompositionIso R E F G Q S hQ hS)
    (dgKernelTensorCompositionNerveIso R E F G Q S)
    (dgRelativeKFlatModuleInclusion R E) (dgRelativeKFlatModuleInclusion R G)
    (dgRelativeKFlatKernelNerve R D E P hP) (dgNerve.map (Morita.kernelTensor R D E P))
    (dgRelativeKFlatModuleInclusion R D) (pair_inclusion R E F G Q S hQ hS).symm
    (dgRelativeKFlatKernelNerve_inclusion R E G (BimoduleTensor.compose R G F E S Q)
      (Bimodule.rightRelativeKFlat_compose R G F E S Q hS hQ)).symm
    (dgRelativeKFlatKernelCompositionIso_inclusion_heq R E F G Q S hQ hS)
    (dgRelativeKFlatKernelNerve_inclusion R D E P hP)
end
end SerrePositivity.InfinityCategories
