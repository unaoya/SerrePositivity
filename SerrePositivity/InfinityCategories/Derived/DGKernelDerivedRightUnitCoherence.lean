module
public import SerrePositivity.InfinityCategories.Derived.ActionRightUnitTransfer
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoPrecompositionReflection
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatComparisonNaturality
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatCompositorCoherence
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatUnitCoherence
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatCompositionRightUnit
/-!
概要：元の指定導来 kernel 合成子 κ の右単位三角式を証明する。
方針：同じ K-flat 比較・単位・合成正方形と ξ 自然性から得て、全前合成で反映する。
規約：kernel の右相対 K-flat 性を明示し、原 Hom の平坦性は追加しない。
使われ方：元の導来 kernel の指定 coherence と一般 cell 模型への移送。
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
local notation "hΔ" => Bimodule.diagonal_rightRelativeKFlat R D
local notation "PΔ" => BimoduleTensor.compose R E D D P (Bimodule.diagonal R D)
local notation "hPΔ" => Bimodule.rightRelativeKFlat_compose R E D D P
  (Bimodule.diagonal R D) hP hΔ
include hP in
/-- 元の指定導来合成子の右単位三角式は、指定 K-flat 分解の前合成後に成立。 -/
lemma dgKernelDerivedInfinity_compIso_right_unit_precomp :
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D D E
        (Bimodule.diagonal R D) P hΔ).precomp (dgRelativeKFlatResolution R D) ≪≫
      (dgKernelDerivedInfinity_bimoduleIso R D E
        (BimoduleTensor.rightBimoduleUnitIso R E D P)).precomp (dgRelativeKFlatResolution R D) =
    ((dgKernelDerivedInfinity_identityIso R D).postcomp
      (dgKernelDerivedInfinity R D E P)).precomp (dgRelativeKFlatResolution R D) := by
  exact rightUnitComparison_transfer (dgRelativeKFlatResolution R D)
    (dgRelativeKFlatResolution R E)
    (dgRelativeKFlatKernelNerve R D D (Bimodule.diagonal R D) hΔ)
    (dgKernelDerivedInfinity R D D (Bimodule.diagonal R D))
    (dgKernelDerivedInfinity R D E P) (dgKernelDerivedInfinity R D E PΔ)
    (dgRelativeKFlatKernelNerve R D E P hP) (dgRelativeKFlatKernelNerve R D E PΔ hPΔ)
    (dgRelativeKFlatKernelNerve_derivedIso R D D (Bimodule.diagonal R D) hΔ)
    (dgRelativeKFlatKernelNerve_derivedIso R D E P hP)
    (dgRelativeKFlatKernelNerve_derivedIso R D E PΔ hPΔ)
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D D E (Bimodule.diagonal R D) P hΔ)
    (dgRelativeKFlatKernelCompositionIso R D D E (Bimodule.diagonal R D) P hΔ hP)
    (dgKernelDerivedInfinity_bimoduleIso R D E (BimoduleTensor.rightBimoduleUnitIso R E D P))
    (dgRelativeKFlatKernelBimoduleIso R D E (BimoduleTensor.rightBimoduleUnitIso R E D P) hPΔ hP)
    (dgKernelDerivedInfinity_identityIso R D) (dgRelativeKFlatKernelIdentityIso R D)
    (dgRelativeKFlatKernelCompositor_iso R D D E (Bimodule.diagonal R D) P hΔ hP)
    (dgRelativeKFlatKernelNerve_derivedIso_bimodule_naturality R D E
      (BimoduleTensor.rightBimoduleUnitIso R E D P) hPΔ hP)
    (dgRelativeKFlatKernelUnit_iso R D)
    (dgRelativeKFlatKernelCompositionIso_right_unit R D E P hP)
include hP in
/-- 元の指定導来合成子と右単位子の作用は、元の指定導来単位の後合成に一致。 -/
lemma dgKernelDerivedInfinity_compIso_right_unit :
    dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D D E
        (Bimodule.diagonal R D) P hΔ ≪≫
      dgKernelDerivedInfinity_bimoduleIso R D E
        (BimoduleTensor.rightBimoduleUnitIso R E D P) =
    (dgKernelDerivedInfinity_identityIso R D).postcomp (dgKernelDerivedInfinity R D E P) := by
  have h := dgKernelDerivedInfinity_compIso_right_unit_precomp R D E P hP
  have hj := (F2.functorIso_precomp_trans
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D D E (Bimodule.diagonal R D) P hΔ)
    (dgKernelDerivedInfinity_bimoduleIso R D E (BimoduleTensor.rightBimoduleUnitIso R E D P))
    (dgRelativeKFlatResolution R D)).trans h
  exact functorIso_precomp_eq_of_isFullyFaithful (dgRelativeKFlatResolution R D)
    (dgRelativeKFlatResolution_precomposition_isFullyFaithful R D
      (dgModuleDerivedInfinityCategory R E)) _ _ hj
end
end SerrePositivity.InfinityCategories
