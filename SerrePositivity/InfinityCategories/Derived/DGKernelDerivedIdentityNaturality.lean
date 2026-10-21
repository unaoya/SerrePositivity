module
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedCompositionNaturality
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
  (P : Bimodule R E D) (hP : Bimodule.rightRelativeKFlat R E D P)
local notation "I" => Bimodule.diagonal R E
local notation "i" => BimoduleCategory.of R E E I
local notation "p" => BimoduleCategory.of R E D P
local notation "IP" => BimoduleTensor.compose R E E D I P
local notation "II" => BimoduleTensor.compose R E E E I I
local notation "hI" => Bimodule.diagonal_rightRelativeKFlat R E
local notation "hIP" => Bimodule.rightRelativeKFlat_compose R E E D I P hI hP
local notation "hII" => Bimodule.rightRelativeKFlat_compose R E E E I I hI hI
include hP in
/-- 元の導来合成子の左単位子に関する第一変数の自然性四角形。 -/
lemma dgKernelDerivedInfinity_identity_first_naturality :
    dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E E IP I hIP ≪≫
      dgKernelDerivedInfinity_bimoduleIso R D E
        (dgKernelBimoduleComposeIso R D E E
          (BimoduleTensor.leftBimoduleUnitIso R E D P) (Iso.refl i)) =
    (dgKernelDerivedInfinity_bimoduleIso R D E
      (BimoduleTensor.leftBimoduleUnitIso R E D P)).postcomp (dgKernelDerivedInfinity R E E I) ≪≫
      dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E E P I hP := by
  have h := dgKernelDerivedInfinity_compIso_naturality R D E E
    (BimoduleTensor.leftBimoduleUnitIso R E D P) (Iso.refl i) hIP hP hI hI
  have he := functorIso_precomp_of_refl
    (dgKernelDerivedInfinity_bimoduleIso R E E (Iso.refl i))
    (dgKernelDerivedInfinity_bimoduleIso_refl R E E i) (dgKernelDerivedInfinity R D E P)
  dsimp only [BimoduleCategory.underlying, BimoduleCategory.of] at h he
  rw [he] at h
  simpa only [Iso.refl_trans] using! h
include hP in
/-- 元の導来合成子の対角の右単位子に関する第二変数の自然性四角形。 -/
lemma dgKernelDerivedInfinity_identity_second_naturality :
    dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E E P II hP ≪≫
      dgKernelDerivedInfinity_bimoduleIso R D E
        (dgKernelBimoduleComposeIso R D E E
          (Iso.refl p) (BimoduleTensor.rightBimoduleUnitIso R E E I)) =
    (dgKernelDerivedInfinity_bimoduleIso R E E
      (BimoduleTensor.rightBimoduleUnitIso R E E I)).precomp (dgKernelDerivedInfinity R D E P) ≪≫
      dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E E P I hP := by
  have h := dgKernelDerivedInfinity_compIso_naturality R D E E
    (Iso.refl p) (BimoduleTensor.rightBimoduleUnitIso R E E I) hP hP hII hI
  have he := functorIso_postcomp_of_refl
    (dgKernelDerivedInfinity_bimoduleIso R D E (Iso.refl p))
    (dgKernelDerivedInfinity_bimoduleIso_refl R D E p) (dgKernelDerivedInfinity R E E II)
  dsimp only [BimoduleCategory.underlying, BimoduleCategory.of] at h he
  rw [he] at h
  simpa only [Iso.refl_trans] using! h
end
end SerrePositivity.InfinityCategories
