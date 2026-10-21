module
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatCommonPath
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatRestrictionSquare
/-!
概要：元の指定合成子を、半自由入力上の制限比較と次の指定 ξ の経路へ同定する。
方針：共通経路等式と、制限比較・変形比較の同じ四角形を合成する。
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
/-- 元の指定合成子は、半自由入力での同じ制限比較・次の ξ・通常合成比較の経路に一致。 -/
lemma dgRelativeKFlatKernelComposition_restriction_hom
    (hP : Bimodule.rightRelativeKFlat R E D P)
    (hQ : Bimodule.rightRelativeKFlat R K E Q) :
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E K P Q hP).hom ≫
      (dgRelativeKFlatKernelRestrictionNerveIso R D K (BimoduleTensor.compose R K E D Q P)
        (Bimodule.rightRelativeKFlat_compose R K E D Q P hQ hP)).hom =
    ((dgRelativeKFlatKernelRestrictionNerveIso R D E P hP).postcomp
      (dgKernelDerivedInfinity R E K Q)).hom ≫
      ((dgRelativeKFlatKernelNerve_derivedIso R E K Q hQ).precomp
        (dgSemifreeToRelativeKFlatNerve R D ≫ dgRelativeKFlatKernelNerve R D E P hP)).hom ≫
      (((dgRelativeKFlatKernelCompositionIso R D E K P Q hP hQ).precomp
        (dgSemifreeToRelativeKFlatNerve R D)).postcomp (dgRelativeKFlatResolution R K)).hom := by
  rw [dgRelativeKFlatKernelComposition_common_path_hom]
  simpa only [Category.assoc] using! (congrArg
    (fun m => m ≫ (((dgRelativeKFlatKernelCompositionIso R D E K P Q hP hQ).precomp
      (dgSemifreeToRelativeKFlatNerve R D)).postcomp (dgRelativeKFlatResolution R K)).hom)
    (dgRelativeKFlatKernelRestrictionNerveIso_derived_square R D E K P Q hP hQ)).symm
end SerrePositivity.InfinityCategories
