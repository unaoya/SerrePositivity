module
public import SerrePositivity.InfinityCategories.Derived.DeformationCompositionSquare
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatCompositorRestriction
/-!
概要：元の指定導来 kernel 合成子と K-flat 比較の二経路の一致を証明する。
方針：同じ制限式と変形比較の正規化を、一般の全関手正方形へ代入する。
規約：元の合成子と比較の値を保持する。使われ方：通常 tensor の coherence の移送。
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
/-- 元の指定合成子の K-flat 制限と、両 kernel の指定比較を通る二経路の射が一致する。 -/
lemma dgRelativeKFlatKernelCompositor_hom
    (hP : Bimodule.rightRelativeKFlat R E D P)
    (hQ : Bimodule.rightRelativeKFlat R K E Q) :
    ((dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E K P Q hP).precomp
      (dgRelativeKFlatResolution R D)).hom ≫
      (dgRelativeKFlatKernelNerve_derivedIso R D K (BimoduleTensor.compose R K E D Q P)
        (Bimodule.rightRelativeKFlat_compose R K E D Q P hQ hP)).hom =
    ((dgRelativeKFlatKernelNerve_derivedIso R D E P hP).postcomp
      (dgKernelDerivedInfinity R E K Q)).hom ≫
      ((dgRelativeKFlatKernelNerve_derivedIso R E K Q hQ).precomp
        (dgRelativeKFlatKernelNerve R D E P hP)).hom ≫
      ((dgRelativeKFlatKernelCompositionIso R D E K P Q hP hQ).postcomp
        (dgRelativeKFlatResolution R K)).hom := by
  refine deformationCompositionSquare_hom (dgRelativeKFlatResolution R D)
    (dgSemifreeToRelativeKFlatNerve R D) (dgRelativeKFlatResolutionAugmentationHomotopy R D)
    (dgKernelDerivedInfinity R D E P) (dgRelativeKFlatKernelNerve R D E P hP)
    (dgRelativeKFlatResolution R E) (dgKernelDerivedInfinity R E K Q)
    (dgKernelDerivedInfinity R D K (BimoduleTensor.compose R K E D Q P))
    (dgRelativeKFlatKernelNerve R E K Q hQ ≫ dgRelativeKFlatResolution R K)
    (dgRelativeKFlatKernelNerve R D K (BimoduleTensor.compose R K E D Q P)
      (Bimodule.rightRelativeKFlat_compose R K E D Q P hQ hP) ≫ dgRelativeKFlatResolution R K)
    (dgRelativeKFlatKernelRestrictionNerveIso R D E P hP)
    (dgRelativeKFlatKernelRestrictionNerveIso R D K (BimoduleTensor.compose R K E D Q P)
      (Bimodule.rightRelativeKFlat_compose R K E D Q P hQ hP))
    (dgRelativeKFlatKernelNerve_derivedIso R D E P hP)
    (dgRelativeKFlatKernelNerve_derivedIso R D K (BimoduleTensor.compose R K E D Q P)
      (Bimodule.rightRelativeKFlat_compose R K E D Q P hQ hP))
    (dgRelativeKFlatKernelNerve_derivedIso R E K Q hQ)
    ((dgRelativeKFlatKernelCompositionIso R D E K P Q hP hQ).postcomp
      (dgRelativeKFlatResolution R K))
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E K P Q hP)
    (dgRelativeKFlatKernelNerve_derivedIso_normalized_hom R D E P hP)
    (dgRelativeKFlatKernelNerve_derivedIso_normalized_hom R D K
      (BimoduleTensor.compose R K E D Q P)
      (Bimodule.rightRelativeKFlat_compose R K E D Q P hQ hP)) ?_
  simpa only [← F2.functorIso_precomp_postcomp] using!
    dgRelativeKFlatKernelComposition_restriction_hom R D E K P Q hP hQ
/-- 元の指定合成子と両 K-flat 比較の正方形は、全関手同型そのものの等式として可換。 -/
lemma dgRelativeKFlatKernelCompositor_iso
    (hP : Bimodule.rightRelativeKFlat R E D P)
    (hQ : Bimodule.rightRelativeKFlat R K E Q) :
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E K P Q hP).precomp
      (dgRelativeKFlatResolution R D) ≪≫
      dgRelativeKFlatKernelNerve_derivedIso R D K (BimoduleTensor.compose R K E D Q P)
        (Bimodule.rightRelativeKFlat_compose R K E D Q P hQ hP) =
    (dgRelativeKFlatKernelNerve_derivedIso R D E P hP).postcomp
      (dgKernelDerivedInfinity R E K Q) ≪≫
      (dgRelativeKFlatKernelNerve_derivedIso R E K Q hQ).precomp
        (dgRelativeKFlatKernelNerve R D E P hP) ≪≫
      (dgRelativeKFlatKernelCompositionIso R D E K P Q hP hQ).postcomp
        (dgRelativeKFlatResolution R K) := by
  apply Iso.ext
  simpa only [Iso.trans_hom] using! dgRelativeKFlatKernelCompositor_hom R D E K P Q hP hQ
end SerrePositivity.InfinityCategories
