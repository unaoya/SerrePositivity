module
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatRawPathTransport
/-!
概要：元の指定導来 kernel 合成子を、同じ K-flat augmentation の共通経路へ同定する。
方針：左右の実経路を元の raw factor の射等式へ移す。
規約：別の合成子や比較を選ばない。使われ方：K-flat 上の二経路の一致と coherence。
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
/-- 元の指定導来合成子と同じ制限比較は、実 K-flat augmentation を通る共通経路に一致。 -/
lemma dgRelativeKFlatKernelComposition_common_path_hom
    (hP : Bimodule.rightRelativeKFlat R E D P)
    (hQ : Bimodule.rightRelativeKFlat R K E Q) :
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E K P Q hP).hom ≫
      (dgRelativeKFlatKernelRestrictionNerveIso R D K (BimoduleTensor.compose R K E D Q P)
        (Bimodule.rightRelativeKFlat_compose R K E D Q P hQ hP)).hom =
    ((dgRelativeKFlatKernelRestrictionNerveIso R E K Q hQ).precomp
      (dgKernelDerivedInfinity R D E P)).hom ≫
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPostcomp (dgRelativeKFlatKernelResolutionAugmentationHomotopy R D E P hP)
          (dgRelativeKFlatKernelNerve R E K Q hQ ≫ dgRelativeKFlatResolution R K))) ≫
      (((dgRelativeKFlatKernelCompositionIso R D E K P Q hP hQ).precomp
        (dgSemifreeToRelativeKFlatNerve R D)).postcomp (dgRelativeKFlatResolution R K)).hom := by
  exact eq_of_heq ((dgRelativeKFlatKernelComposition_left_raw_hom_heq
    R D E K P Q hP hQ).trans
      ((heq_of_eq (dgKernelDerivedInfinity_compIso_rawFactor_hom R D E K P Q hP)).trans
        (dgRelativeKFlatKernelComposition_right_raw_hom_heq R D E K P Q hP hQ).symm))
end SerrePositivity.InfinityCategories
