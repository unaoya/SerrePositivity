module

public import SerrePositivity.InfinityCategories.F2.Ind.SectionFamilyProductBase
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationInfinity

/-!
概要：通常の under 圏上の切断を、元のもう一方の底の上の族として構成する。
方針：元の積上の射影を固定し、under 圏の反変な制限を同じパラメータへ持ち上げる。
規約：通常の圏上の全ての射を実際の底上の射として使う。
使われ方：coherent 前層図式の strict な fibration 図式への置き換え。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Category.{u} I] {B E : SSet.{u}} (p : E ⟶ B ⊗ nerve I)

/-- 同じ under 圏の上の切断を元の底で動かした族。 -/
def underSectionFamily (i : I) : SSet.{u} :=
  parametrizedSections p (sectionFamilyProductBase B (nerveMap (Under.forget i)))

/-- 同じ under 切断の元の底への射影。 -/
def underSectionFamilyProjection (i : I) : underSectionFamily p i ⟶ B :=
  parametrizedSectionsProjection p _

instance underSectionFamilyProjection_leftFibration [LeftFibration p] (i : I) :
    LeftFibration (underSectionFamilyProjection p i) :=
  parametrizedSectionsProjection_leftFibration p _

instance underSectionFamily_quasicategory [Quasicategory B] [LeftFibration p] (i : I) :
    Quasicategory (underSectionFamily p i) :=
  quasicategory_of_innerFibration (underSectionFamilyProjection p i)

/-- 元の under 圏の制限は、元の底を保つ実際の写像。 -/
def underSectionFamilyMap {i j : I} (f : i ⟶ j) : underSectionFamily p i ⟶ underSectionFamily p j :=
  parametrizedSectionsPre p
    (sectionFamilyProductBase B (nerveMap (Under.forget i)))
    (sectionFamilyProductBase B (nerveMap (Under.forget j)))
    (nerveUnderMap f) (sectionFamilyProductBase_under B f)

/-- 同じ制限は元の底の射影を厳密に保つ。 -/
lemma underSectionFamilyMap_projection {i j : I} (f : i ⟶ j) :
    underSectionFamilyMap p f ≫ underSectionFamilyProjection p j =
      underSectionFamilyProjection p i := parametrizedSectionsPre_projection _ _ _ _ _

end SerrePositivity.InfinityCategories.F2.Ind
