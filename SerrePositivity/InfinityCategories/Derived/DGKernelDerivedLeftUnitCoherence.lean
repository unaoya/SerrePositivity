module
public import SerrePositivity.InfinityCategories.Derived.ActionLeftUnitFromPentagon
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedIdentityNaturality
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedRightUnitCoherence
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedPentagonCoherence
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
  (P : Bimodule R E D) (hP : Bimodule.rightRelativeKFlat R E D P)
local notation "I" => Bimodule.diagonal R E
local notation "i" => BimoduleCategory.of R E E I
local notation "p" => BimoduleCategory.of R E D P
local notation "IP" => BimoduleTensor.compose R E E D I P
local notation "II" => BimoduleTensor.compose R E E E I I
local notation "hI" => Bimodule.diagonal_rightRelativeKFlat R E
local notation "hIP" => Bimodule.rightRelativeKFlat_compose R E E D I P hI hP
include hP in
/-- 元の指定導来合成子と左単位子の作用は、元の指定導来単位の制限に一致。 -/
lemma dgKernelDerivedInfinity_compIso_left_unit :
    dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E E P I hP ≪≫
      dgKernelDerivedInfinity_bimoduleIso R D E (BimoduleTensor.leftBimoduleUnitIso R E D P) =
    (dgKernelDerivedInfinity_identityIso R E).precomp (dgKernelDerivedInfinity R D E P) := by
  exact leftUnitComparison_from_pentagon (dgKernelDerivedInfinity R D E P)
    (dgKernelDerivedInfinity R E E I) (dgKernelDerivedInfinity R D E IP)
    (dgKernelDerivedInfinity R E E II)
    (dgKernelDerivedInfinity R D E (BimoduleTensor.compose R E E D I IP))
    (dgKernelDerivedInfinity R D E (BimoduleTensor.compose R E E D II P))
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E E P I hP)
    (dgKernelDerivedInfinity_bimoduleIso R D E (BimoduleTensor.leftBimoduleUnitIso R E D P))
    (dgKernelDerivedInfinity_bimoduleIso R E E (BimoduleTensor.rightBimoduleUnitIso R E E I))
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R E E E I I hI)
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E E IP I hIP)
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E E P II hP)
    (dgKernelDerivedInfinity_bimoduleIso R D E
      (BimoduleTensor.associatorIso R E E E D I I P))
    (dgKernelDerivedInfinity_bimoduleIso R D E (dgKernelBimoduleComposeIso R D E E
      (BimoduleTensor.leftBimoduleUnitIso R E D P) (Iso.refl i)))
    (dgKernelDerivedInfinity_bimoduleIso R D E (dgKernelBimoduleComposeIso R D E E
      (Iso.refl p) (BimoduleTensor.rightBimoduleUnitIso R E E I)))
    (dgKernelDerivedInfinity_identityIso R E)
    (dgKernelDerivedInfinity_identity_triangle R D E P)
    (dgKernelDerivedInfinity_identity_first_naturality R D E P hP)
    (dgKernelDerivedInfinity_identity_second_naturality R D E P hP)
    (dgKernelDerivedInfinity_compIso_right_unit R E E I hI)
    (dgKernelDerivedInfinity_compIso_pentagon R D E E E P I I hP hI hI)
end
end SerrePositivity.InfinityCategories
