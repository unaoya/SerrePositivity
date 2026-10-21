module
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedIdentityTriangle
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoWhiskerRefl
/-!
概要：二つの対角 kernel を含む三角式と、同じ単位子に関する指定比較の自然性。
方針：元の三角式・指定比較の自然性・同じ恒等同型の前後合成を使う。
規約：原 Hom の平坦性を追加しない。使われ方：元の左単位三角式の回収。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  (P : Bimodule R E D)
local notation "I" => Bimodule.diagonal R E
local notation "i" => BimoduleCategory.of R E E I
local notation "p" => BimoduleCategory.of R E D P
local notation "IP" => BimoduleTensor.compose R E E D I P
local notation "II" => BimoduleTensor.compose R E E E I I
local notation "a" => BimoduleTensor.associatorIso R E E E D I I P
local notation "l" => dgKernelBimoduleComposeIso R D E E
  (BimoduleTensor.leftBimoduleUnitIso R E D P) (Iso.refl i)
local notation "q" => dgKernelBimoduleComposeIso R D E E
  (Iso.refl p) (BimoduleTensor.rightBimoduleUnitIso R E E I)
/-- 二つの対角 kernel を含む元の dg 三角式の通常作用への像。 -/
lemma dgKernelTensorNerve_identity_triangle :
    dgKernelTensorIsoNerveOfBimoduleIso R D E a ≪≫
      dgKernelTensorIsoNerveOfBimoduleIso R D E l =
    dgKernelTensorIsoNerveOfBimoduleIso R D E q := by
  rw [← dgKernelTensorIsoNerveOfBimoduleIso_trans, dgKernelBimodule_identity_triangle]
/-- 元の通常合成比較の左単位子に関する第一変数の自然性四角形。 -/
lemma dgKernelTensorNerve_identity_first_naturality :
    dgKernelTensorCompositionNerveIso R D E E IP I ≪≫
      dgKernelTensorIsoNerveOfBimoduleIso R D E l =
    (dgKernelTensorIsoNerveOfBimoduleIso R D E
      (BimoduleTensor.leftBimoduleUnitIso R E D P)).postcomp
        (dgNerve.map (Morita.kernelTensor R E E I)) ≪≫
      dgKernelTensorCompositionNerveIso R D E E P I := by
  have h := dgKernelTensorCompositionNerveIso_naturality R D E E
    (BimoduleTensor.leftBimoduleUnitIso R E D P) (Iso.refl i)
  have he := functorIso_precomp_of_refl (dgKernelTensorIsoNerveOfBimoduleIso R E E (Iso.refl i))
    (dgKernelTensorIsoNerveOfBimoduleIso_refl R E E i)
    (dgNerve.map (Morita.kernelTensor R D E P))
  dsimp only [BimoduleCategory.underlying, BimoduleCategory.of] at h he
  rw [he] at h
  simpa only [Iso.refl_trans] using! h
/-- 元の通常合成比較の対角の右単位子に関する第二変数の自然性四角形。 -/
lemma dgKernelTensorNerve_identity_second_naturality :
    dgKernelTensorCompositionNerveIso R D E E P II ≪≫
      dgKernelTensorIsoNerveOfBimoduleIso R D E q =
    (dgKernelTensorIsoNerveOfBimoduleIso R E E
      (BimoduleTensor.rightBimoduleUnitIso R E E I)).precomp
        (dgNerve.map (Morita.kernelTensor R D E P)) ≪≫
      dgKernelTensorCompositionNerveIso R D E E P I := by
  have h := dgKernelTensorCompositionNerveIso_naturality R D E E
    (Iso.refl p) (BimoduleTensor.rightBimoduleUnitIso R E E I)
  have he := functorIso_postcomp_of_refl (dgKernelTensorIsoNerveOfBimoduleIso R D E (Iso.refl p))
    (dgKernelTensorIsoNerveOfBimoduleIso_refl R D E p)
    (dgNerve.map (Morita.kernelTensor R E E II))
  dsimp only [BimoduleCategory.underlying, BimoduleCategory.of] at h he
  rw [he] at h
  simpa only [Iso.refl_trans] using! h
end
end SerrePositivity.InfinityCategories
