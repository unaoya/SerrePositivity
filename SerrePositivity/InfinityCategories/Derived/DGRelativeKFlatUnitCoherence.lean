module
public import SerrePositivity.InfinityCategories.Derived.DeformationUnitSquare
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatAugmentationRetract
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatOriginalUnitSquare
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelAugmentationSquare
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatComparisonPath
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 元の指定 K-flat 比較と通常対角単位の経路は、元の指定導来単位の分解制限に一致。 -/
lemma dgRelativeKFlatKernelUnit_hom :
    (dgRelativeKFlatKernelNerve_derivedIso R D D (Bimodule.diagonal R D)
      (Bimodule.diagonal_rightRelativeKFlat R D)).hom ≫
      ((dgRelativeKFlatKernelIdentityIso R D).postcomp (dgRelativeKFlatResolution R D)).hom =
    ((dgKernelDerivedInfinity_identityIso R D).precomp (dgRelativeKFlatResolution R D)).hom := by
  exact deformationUnitSquare_hom (dgRelativeKFlatResolution R D)
    (dgSemifreeToRelativeKFlatNerve R D) (dgRelativeKFlatResolutionAugmentationHomotopy R D)
    (dgRelativeKFlatAugmentationRetractIso R D)
    (dgKernelDerivedInfinity R D D (Bimodule.diagonal R D))
    (dgRelativeKFlatKernelNerve R D D (Bimodule.diagonal R D)
      (Bimodule.diagonal_rightRelativeKFlat R D))
    (dgRelativeKFlatKernelRestrictionNerveIso R D D (Bimodule.diagonal R D)
      (Bimodule.diagonal_rightRelativeKFlat R D))
    (dgRelativeKFlatKernelResolutionAugmentationHomotopy R D D (Bimodule.diagonal R D)
      (Bimodule.diagonal_rightRelativeKFlat R D))
    (deformationRetractTriangle_hom (dgRelativeKFlatResolution R D)
      (dgSemifreeToRelativeKFlatNerve R D) (dgRelativeKFlatResolutionAugmentationHomotopy R D)
      (dgRelativeKFlatAugmentationRetractIso R D)
      (dgRelativeKFlatResolution_precomposition_isFullyFaithful R D
        (dgModuleDerivedInfinityCategory R D))
      (dgRelativeKFlatAugmentationRetractIso_postcomp_hom R D))
    (dgRelativeKFlatKernelRestrictionNerveIso_augmentation R D D (Bimodule.diagonal R D)
      (Bimodule.diagonal_rightRelativeKFlat R D))
    (dgRelativeKFlatKernelIdentityIso R D) (dgKernelDerivedInfinity_identityIso R D)
    (dgRelativeKFlatKernelNerve_derivedIso R D D (Bimodule.diagonal R D)
      (Bimodule.diagonal_rightRelativeKFlat R D))
    (dgKernelDerivedInfinity_identityIso_kflat_augmentation R D)
    (dgRelativeKFlatKernelNerve_derivedIso_normalized_hom R D D (Bimodule.diagonal R D)
      (Bimodule.diagonal_rightRelativeKFlat R D))
/-- 通常 K-flat 単位と元の導来単位の比較は、指定全関手同型そのものの等式で可換。 -/
lemma dgRelativeKFlatKernelUnit_iso :
    dgRelativeKFlatKernelNerve_derivedIso R D D (Bimodule.diagonal R D)
      (Bimodule.diagonal_rightRelativeKFlat R D) ≪≫
      (dgRelativeKFlatKernelIdentityIso R D).postcomp (dgRelativeKFlatResolution R D) =
    (dgKernelDerivedInfinity_identityIso R D).precomp (dgRelativeKFlatResolution R D) := by
  apply Iso.ext
  simpa only [Iso.trans_hom] using! dgRelativeKFlatKernelUnit_hom R D
end SerrePositivity.InfinityCategories
