module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ActionRightUnitTransfer
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoPrecompositionReflection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatComparisonNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatCompositorCoherence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatUnitCoherence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatCompositionRightUnit
/-!
概要：元の指定導来 kernel 合成子 κ の右単位三角式を証明する。
方針：同じ K-flat 比較・単位・合成正方形と ξ 自然性から得て、全前合成で反映する。
規約：kernel の右相対 K-flat 性を明示し、原 Hom の平坦性は追加しない。
使われ方：元の導来 kernel の指定 coherence と一般 cell 模型への移送。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P)
local notation "hΔ" => _root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal_rightRelativeKFlat R D
local notation "PΔ" => _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R E D D P (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R D)
local notation "hPΔ" => _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R E D D P
  (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R D) hP hΔ
include hP in
/-- 元の指定導来合成子の右単位三角式は、指定 K-flat 分解の前合成後に成立。 -/
lemma dgKernelDerivedInfinity_compIso_right_unit_precomp :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D D E
        (Bimodule.diagonal R D) P hΔ).precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D) ≪≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E
        (BimoduleTensor.rightBimoduleUnitIso R E D P)).precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D) =
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identityIso R D).postcomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P)).precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.rightUnitComparison_transfer (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D D (Bimodule.diagonal R D) hΔ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D D (Bimodule.diagonal R D))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E PΔ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P hP) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E PΔ hPΔ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D D (Bimodule.diagonal R D) hΔ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D E P hP)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D E PΔ hPΔ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D D E (Bimodule.diagonal R D) P hΔ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R D D E (Bimodule.diagonal R D) P hΔ hP)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E (BimoduleTensor.rightBimoduleUnitIso R E D P))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleIso R D E (BimoduleTensor.rightBimoduleUnitIso R E D P) hPΔ hP)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identityIso R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelIdentityIso R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositor_iso R D D E (Bimodule.diagonal R D) P hΔ hP)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso_bimodule_naturality R D E
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightBimoduleUnitIso R E D P) hPΔ hP)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelUnit_iso R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso_right_unit R D E P hP)
include hP in
/-- 元の指定導来合成子と右単位子の作用は、元の指定導来単位の後合成に一致。 -/
lemma dgKernelDerivedInfinity_compIso_right_unit :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D D E
        (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R D) P hΔ ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightBimoduleUnitIso R E D P) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identityIso R D).postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P) := by
  have h := dgKernelDerivedInfinity_compIso_right_unit_precomp R D E P hP
  have hj := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D D E (Bimodule.diagonal R D) P hΔ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E (BimoduleTensor.rightBimoduleUnitIso R E D P))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D)).trans h
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_eq_of_isFullyFaithful (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution_precomposition_isFullyFaithful R D
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R E)) _ _ hj
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
