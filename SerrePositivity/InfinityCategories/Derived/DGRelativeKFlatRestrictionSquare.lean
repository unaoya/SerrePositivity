module
public import SerrePositivity.InfinityCategories.Derived.DeformationRestrictionSquare
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatComparisonPath
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelAugmentationSquare
/-!
概要：元の kernel 制限比較と次の K-flat 比較の四角形を、同じ augmentation へ同定する。
方針：指定 ξ の射の正規化と、保存済みの実 augmentation 正方形を一般交換則へ代入する。
規約：指定比較と実円柱の値を保持する。使われ方：元の合成子の二経路照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D E K : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R K] [Small.{u} K]
  (P : Bimodule R E D) (Q : Bimodule R K E)
/-- 同じ制限比較と次の指定 ξ の経路は、次の制限比較と元の augmentation の経路。 -/
lemma dgRelativeKFlatKernelRestrictionNerveIso_derived_square
    (hP : Bimodule.rightRelativeKFlat R E D P)
    (hQ : Bimodule.rightRelativeKFlat R K E Q) :
    ((dgRelativeKFlatKernelRestrictionNerveIso R D E P hP).postcomp
      (dgKernelDerivedInfinity R E K Q)).hom ≫
      ((dgRelativeKFlatKernelNerve_derivedIso R E K Q hQ).precomp
        (dgSemifreeToRelativeKFlatNerve R D ≫ dgRelativeKFlatKernelNerve R D E P hP)).hom =
    ((dgRelativeKFlatKernelRestrictionNerveIso R E K Q hQ).precomp
      (dgKernelDerivedInfinity R D E P)).hom ≫
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPostcomp (dgRelativeKFlatKernelResolutionAugmentationHomotopy R D E P hP)
          (dgRelativeKFlatKernelNerve R E K Q hQ ≫ dgRelativeKFlatResolution R K))) := by
  exact deformationRestrictionSquare_hom (dgRelativeKFlatResolution R E)
    (dgSemifreeToRelativeKFlatNerve R E) (dgRelativeKFlatResolutionAugmentationHomotopy R E)
    (dgKernelDerivedInfinity R D E P)
    (dgSemifreeToRelativeKFlatNerve R D ≫ dgRelativeKFlatKernelNerve R D E P hP)
    (dgKernelDerivedInfinity R E K Q)
    (dgRelativeKFlatKernelNerve R E K Q hQ ≫ dgRelativeKFlatResolution R K)
    (dgRelativeKFlatKernelRestrictionNerveIso R D E P hP)
    (dgRelativeKFlatKernelRestrictionNerveIso R E K Q hQ)
    (dgRelativeKFlatKernelNerve_derivedIso R E K Q hQ)
    (dgRelativeKFlatKernelResolutionAugmentationHomotopy R D E P hP)
    (dgRelativeKFlatKernelNerve_derivedIso_normalized_hom R E K Q hQ)
    (dgRelativeKFlatKernelRestrictionNerveIso_augmentation R D E P hP)
end SerrePositivity.InfinityCategories
