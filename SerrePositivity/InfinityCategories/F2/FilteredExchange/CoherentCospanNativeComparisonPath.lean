module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeComparisonEquivalence
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.IntervalReplacementPathRestriction

/-!
概要：元の native 比較を通る区間 path は、元の native な指定可換同型に一致する。
方針：比較を作った同じ全円柱と二射影の厳密な式を読み戻す。
規約：元の path の指定値を保持。使われ方：余極限後の錐の脚比較の最終整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)
local notation "nf" => coherentTotalMapNativeValueDown X Z
  (coherentTransformationTotalMap X Z C.fromLeft)
local notation "ng" => coherentTotalMapNativeValueDown Y Z
  (coherentTransformationTotalMap Y Z C.fromRight)
local notation "nl" => coherentTotalMapNativeValueDown F X
  (coherentTransformationTotalMap F X C.toLeft)
local notation "nr" => coherentTotalMapNativeValueDown F Y
  (coherentTransformationTotalMap F Y C.toRight)
local notation "n" => coherentCospanConeNativeComparison F X Y Z C

/-- 元の比較による区間 path の制限は、元の native 指定可換同型と型付きで一致。 -/
lemma coherentCospanNativeComparisonPathIso_heq :
    HEq ((intervalPullbackPathIso nf ng).precomp n)
      (coherentCospanConeNativePathDownIso F X Y Z C) := by
  have hp := intervalPullbackHomotopyPoint_pathIso_heq nf ng nl nr
    (coherentCospanConeNativeComparisonHomotopy F X Y Z C)
  have he : functorIsoOfSimplicialHomotopy
      (coherentCospanConeNativeComparisonHomotopy F X Y Z C) =
        coherentCospanConeNativePathDownIso F X Y Z C := by
    apply Iso.ext
    exact coherentCospanConeNativeComparisonHomotopy_hom F X Y Z C
  exact hp.trans (heq_of_eq he)

end SerrePositivity.InfinityCategories.F2
