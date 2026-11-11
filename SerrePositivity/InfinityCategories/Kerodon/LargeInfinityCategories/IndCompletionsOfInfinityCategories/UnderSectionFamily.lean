module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.SectionFamilyProductBase
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity

/-!
概要：通常の under 圏上の切断を、元のもう一方の底の上の族として構成する。
方針：元の積上の射影を固定し、under 圏の反変な制限を同じパラメータへ持ち上げる。
規約：通常の圏上の全ての射を実際の底上の射として使う。
使われ方：coherent 前層図式の strict な fibration 図式への置き換え。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [Category.{u} I] {B E : SSet.{u}} (p : E ⟶ B ⊗ nerve I)

/-- 同じ under 圏の上の切断を元の底で動かした族。 -/
def underSectionFamily (i : I) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSections p (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.sectionFamilyProductBase B (nerveMap (Under.forget i)))

/-- 同じ under 切断の元の底への射影。 -/
def underSectionFamilyProjection (i : I) : underSectionFamily p i ⟶ B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsProjection p _

instance underSectionFamilyProjection_leftFibration [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (i : I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (underSectionFamilyProjection p i) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsProjection_leftFibration p _

instance underSectionFamily_quasicategory [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (i : I) :
    Quasicategory (underSectionFamily p i) :=
  quasicategory_of_innerFibration (underSectionFamilyProjection p i)

/-- 元の under 圏の制限は、元の底を保つ実際の写像。 -/
def underSectionFamilyMap {i j : I} (f : i ⟶ j) : underSectionFamily p i ⟶ underSectionFamily p j :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsPre p
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.sectionFamilyProductBase B (nerveMap (Under.forget i)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.sectionFamilyProductBase B (nerveMap (Under.forget j)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap f) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.sectionFamilyProductBase_under B f)

/-- 同じ制限は元の底の射影を厳密に保つ。 -/
lemma underSectionFamilyMap_projection {i j : I} (f : i ⟶ j) :
    underSectionFamilyMap p f ≫ underSectionFamilyProjection p j =
      underSectionFamilyProjection p i := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsPre_projection _ _ _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
