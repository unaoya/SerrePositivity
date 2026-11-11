module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatCommonPath
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatRestrictionSquare
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
variable (R : Type u) [CommRing R] (D E K : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R K] [Small.{u} K]
  (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R K E)
/-- 元の指定合成子は、半自由入力での同じ制限比較・次の ξ・通常合成比較の経路に一致。 -/
lemma dgRelativeKFlatKernelComposition_restriction_hom
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P)
    (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R K E Q) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E K P Q hP).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelRestrictionNerveIso R D K (BimoduleTensor.compose R K E D Q P)
        (_root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R K E D Q P hQ hP)).hom =
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelRestrictionNerveIso R D E P hP).postcomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E K Q)).hom ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R E K Q hQ).precomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P hP)).hom ≫
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R D E K P Q hP hQ).precomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D)).postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R K)).hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelComposition_common_path_hom]
  simpa only [Category.assoc] using! (congrArg
    (fun m => m ≫ (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R D E K P Q hP hQ).precomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D)).postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R K)).hom)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelRestrictionNerveIso_derived_square R D E K P Q hP hQ)).symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories
