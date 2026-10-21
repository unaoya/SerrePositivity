module
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatCompositionWhisker
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelBimoduleIso
public import SerrePositivity.InfinityCategories.Derived.DGKernelCompositionNervePentagon
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoLiftedPathReflection
/-!
概要：K-flat の元の指定 kernel 合成比較の五角式を、全関手同型として証明する。
方針：実完全充満包含後の各辺を同じ通常五角の制限へ回収し、等式を反映する。
規約：原 Hom の平坦性を追加しない。使われ方：元の導来合成子への coherence の移送。
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
variable (P : Bimodule R E D) (Q : Bimodule R F E) (S : Bimodule R G F)
    (hP : Bimodule.rightRelativeKFlat R E D P) (hQ : Bimodule.rightRelativeKFlat R F E Q)
    (hS : Bimodule.rightRelativeKFlat R G F S)
local notation "QP" => BimoduleTensor.compose R F E D Q P
local notation "SQ" => BimoduleTensor.compose R G F E S Q
local notation "hQP" => Bimodule.rightRelativeKFlat_compose R F E D Q P hQ hP
local notation "hSQ" => Bimodule.rightRelativeKFlat_compose R G F E S Q hS hQ
local notation "hSQP" => Bimodule.rightRelativeKFlat_compose R G E D SQ P hSQ hP
local notation "hSQP'" => Bimodule.rightRelativeKFlat_compose R G F D S QP hS hQP
/-- 元の K-flat kernel 合成比較は、同じ双加群結合子と五角経路を満たす。 -/
lemma dgRelativeKFlatKernelCompositionIso_pentagon :
    (dgRelativeKFlatKernelCompositionIso R D E F P Q hP hQ).postcomp
        (dgRelativeKFlatKernelNerve R F G S hS) ≪≫
      dgRelativeKFlatKernelCompositionIso R D F G QP S hQP hS =
    (dgRelativeKFlatKernelCompositionIso R E F G Q S hQ hS).precomp
        (dgRelativeKFlatKernelNerve R D E P hP) ≪≫
      dgRelativeKFlatKernelCompositionIso R D E G P SQ hP hSQ ≪≫
      dgRelativeKFlatKernelBimoduleIso R D G
        (BimoduleTensor.associatorIso R G F E D S Q P) hSQP hSQP' := by
  have hf : ((dgRelativeKFlatKernelNerve R D E P hP ≫
      dgRelativeKFlatKernelNerve R E F Q hQ) ≫ dgRelativeKFlatKernelNerve R F G S hS) ≫
      dgRelativeKFlatModuleInclusion R G = dgRelativeKFlatModuleInclusion R D ≫
      ((dgNerve.map (Morita.kernelTensor R D E P) ≫
        dgNerve.map (Morita.kernelTensor R E F Q)) ≫
          dgNerve.map (Morita.kernelTensor R F G S)) := by
    rw [Category.assoc, dgRelativeKFlatKernelNerve_inclusion, ← Category.assoc,
      pair_inclusion R D E F P Q hP hQ, Category.assoc]
  have hg := pair_inclusion R D F G QP S hQP hS
  have hh := pair_inclusion R D E G P SQ hP hSQ
  have ht := dgRelativeKFlatKernelNerve_inclusion R D G
    (BimoduleTensor.compose R G E D SQ P) hSQP
  have hk := dgRelativeKFlatKernelNerve_inclusion R D G
    (BimoduleTensor.compose R G F D S QP) hSQP'
  have he := congrArg (fun e => FunctorIso.precomp e (dgRelativeKFlatModuleInclusion R D))
    (dgKernelTensorCompositionNerveIso_pentagon R D E F G P Q S)
  simp only [F2.functorIso_precomp_trans] at he
  exact functorIso_two_three_reflect_postcomp (dgRelativeKFlatModuleInclusion R G)
    (isFullyFaithful_fullSubcomplexOnVertices_ι (dgModuleNerve R G)
      (dgModuleRelativeKFlatVertex R G)) _ _ _ _ _ _ _ _ _ _ hf hg hh ht hk
    (dgRelativeKFlatKernelComposition_postcomp_inclusion_heq R D E F G P Q S hP hQ hS)
    (dgRelativeKFlatKernelCompositionIso_inclusion_heq R D F G QP S hQP hS)
    (dgRelativeKFlatKernelComposition_precomp_inclusion_heq R D E F G P Q S hP hQ hS)
    (dgRelativeKFlatKernelCompositionIso_inclusion_heq R D E G P SQ hP hSQ)
    (dgRelativeKFlatKernelBimoduleIso_inclusion_heq R D G
      (BimoduleTensor.associatorIso R G F E D S Q P) hSQP hSQP') he
end
end SerrePositivity.InfinityCategories
