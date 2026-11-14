module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.DeformationUnitSquare
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGRelativeKFlatAugmentationRetract
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGRelativeKFlatOriginalUnitSquare
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGRelativeKFlatKernelAugmentationSquare
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGRelativeKFlatComparisonPath
/-!
概要：元の導来対角単位と通常 K-flat 単位を、同じ指定比較の全関手正方形で照合する。
方針：同じ戻り同型の補助三角式と、元の augmentation・単位の正方形を代入する。
規約：元の指定単位と比較の値を保持する。使われ方：kernel の triangle・pentagon の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- 元の指定 K-flat 比較と通常対角単位の経路は、元の指定導来単位の分解制限に一致。 -/
lemma dgRelativeKFlatKernelUnit_hom :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D D (Bimodule.diagonal R D)
      (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal_rightRelativeKFlat R D)).hom ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelIdentityIso R D).postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D)).hom =
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identityIso R D).precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D)).hom := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationUnitSquare_hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolutionAugmentationHomotopy R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatAugmentationRetractIso R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D D (Bimodule.diagonal R D))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D D (Bimodule.diagonal R D)
      (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal_rightRelativeKFlat R D))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelRestrictionNerveIso R D D (Bimodule.diagonal R D)
      (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal_rightRelativeKFlat R D))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelResolutionAugmentationHomotopy R D D (Bimodule.diagonal R D)
      (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal_rightRelativeKFlat R D))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationRetractTriangle_hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolutionAugmentationHomotopy R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatAugmentationRetractIso R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution_precomposition_isFullyFaithful R D
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatAugmentationRetractIso_postcomp_hom R D))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelRestrictionNerveIso_augmentation R D D (Bimodule.diagonal R D)
      (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal_rightRelativeKFlat R D))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelIdentityIso R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identityIso R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D D (Bimodule.diagonal R D)
      (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal_rightRelativeKFlat R D))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identityIso_kflat_augmentation R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso_normalized_hom R D D (Bimodule.diagonal R D)
      (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal_rightRelativeKFlat R D))
/-- 通常 K-flat 単位と元の導来単位の比較は、指定全関手同型そのものの等式で可換。 -/
lemma dgRelativeKFlatKernelUnit_iso :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D D (Bimodule.diagonal R D)
      (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal_rightRelativeKFlat R D) ≪≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelIdentityIso R D).postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identityIso R D).precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D) := by
  apply Iso.ext
  simpa only [Iso.trans_hom] using! dgRelativeKFlatKernelUnit_hom R D
end SerrePositivity.InfinityCategories.Project.DerivedCategories
