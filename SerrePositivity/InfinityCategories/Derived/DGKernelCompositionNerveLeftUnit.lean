module
public import SerrePositivity.InfinityCategories.Derived.ActionLeftUnitFromPentagon
public import SerrePositivity.InfinityCategories.Derived.DGKernelNerveIdentityCoherence
public import SerrePositivity.InfinityCategories.Derived.DGKernelCompositionNerveRightUnit
public import SerrePositivity.InfinityCategories.Derived.DGKernelCompositionNervePentagon
/-!
概要：元の指定合成比較と同じ左単位子の作用の三角式を証明する。
方針：同じ二重対角 kernel の三角像・自然性・五角式・右単位を使う。
規約：元の指定値を保ち、原 Hom の平坦性を追加しない。
使われ方：kernel の単位 coherence と一般 cell 模型への移送。
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
/-- 元の通常合成比較と左単位子の作用は、元の通常単位の制限に一致。 -/
lemma dgKernelTensorCompositionNerveIso_left_unit :
    dgKernelTensorCompositionNerveIso R D E E P I ≪≫
      dgKernelTensorIsoNerveOfBimoduleIso R D E (BimoduleTensor.leftBimoduleUnitIso R E D P) =
    (dgKernelIdentityNerveIso R E).precomp (dgNerve.map (Morita.kernelTensor R D E P)) := by
  exact leftUnitComparison_from_pentagon (dgNerve.map (Morita.kernelTensor R D E P))
    (dgNerve.map (Morita.kernelTensor R E E I))
    (dgNerve.map (Morita.kernelTensor R D E IP)) (dgNerve.map (Morita.kernelTensor R E E II))
    (dgNerve.map (Morita.kernelTensor R D E (BimoduleTensor.compose R E E D I IP)))
    (dgNerve.map (Morita.kernelTensor R D E (BimoduleTensor.compose R E E D II P)))
    (dgKernelTensorCompositionNerveIso R D E E P I)
    (dgKernelTensorIsoNerveOfBimoduleIso R D E (BimoduleTensor.leftBimoduleUnitIso R E D P))
    (dgKernelTensorIsoNerveOfBimoduleIso R E E (BimoduleTensor.rightBimoduleUnitIso R E E I))
    (dgKernelTensorCompositionNerveIso R E E E I I)
    (dgKernelTensorCompositionNerveIso R D E E IP I)
    (dgKernelTensorCompositionNerveIso R D E E P II)
    (dgKernelTensorIsoNerveOfBimoduleIso R D E (BimoduleTensor.associatorIso R E E E D I I P))
    (dgKernelTensorIsoNerveOfBimoduleIso R D E (dgKernelBimoduleComposeIso R D E E
      (BimoduleTensor.leftBimoduleUnitIso R E D P) (Iso.refl i)))
    (dgKernelTensorIsoNerveOfBimoduleIso R D E (dgKernelBimoduleComposeIso R D E E
      (Iso.refl p) (BimoduleTensor.rightBimoduleUnitIso R E E I)))
    (dgKernelIdentityNerveIso R E) (dgKernelTensorNerve_identity_triangle R D E P)
    (dgKernelTensorNerve_identity_first_naturality R D E P)
    (dgKernelTensorNerve_identity_second_naturality R D E P)
    (dgKernelTensorCompositionNerveIso_right_unit R E E I)
    (dgKernelTensorCompositionNerveIso_pentagon R D E E E P I I)
end
end SerrePositivity.InfinityCategories
