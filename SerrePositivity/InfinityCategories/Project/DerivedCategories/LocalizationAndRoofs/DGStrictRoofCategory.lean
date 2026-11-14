module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGClosedRoofRefinements
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-! # 元の閉分母と閉分子の厳密屋根圏

概要：元の閉実分母と同じ始域の閉分子を持つ屋根、および厳密な細分を通常の圏にする。
方針：閉分母の始域関手の costructured arrow を取り、分母・分子の二射影を与える。
規約：実屋根との同値や cofinality は仮定しない。使われ方：実屋根の辺と高次射列の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 閉実分母 q→x と同じ始域の閉分子 q→y を持つ厳密屋根の通常の圏。 -/
abbrev DGStrictRoofs (P : Set D) (x y : D) :=
  CostructuredArrow (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorSource A D P x)
    (ForgetEnrichment.of (Complex A) y)

/-- 厳密屋根の元の閉分母への射影。 -/
def dgStrictRoofDenominator (P : Set D) (x y : D) :
    DGStrictRoofs A D P x y ⥤ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x :=
  CostructuredArrow.proj _ _

/-- 厳密屋根の閉分子を、同じ固定終点の通常の over 対象として読む。 -/
def dgStrictRoofNumerator (P : Set D) (x y : D) :
    DGStrictRoofs A D P x y ⥤ Over (ForgetEnrichment.of (Complex A) y) where
  obj s := Over.mk s.hom
  map r := Over.homMk ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorSource A D P x).map r.left)
    (CostructuredArrow.w r)

/-- 指定された元の閉分母と閉分子は、厳密屋根の指定対象を与える。 -/
def dgStrictRoofMk (P : Set D) (x y : D) (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x)
    (f : s.obj.left ⟶ ForgetEnrichment.of (Complex A) y) : DGStrictRoofs A D P x y :=
  CostructuredArrow.mk f

/-- 指定厳密閉細分と閉分子は、同じ厳密屋根圏の射を与える。 -/
def dgStrictRoofRefine (P : Set D) (x y : D)
    {s t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x} (r : s ⟶ t)
    (f : t.obj.left ⟶ ForgetEnrichment.of (Complex A) y) :
    dgStrictRoofMk A D P x y s (r.hom.left ≫ f) ⟶ dgStrictRoofMk A D P x y t f :=
  CostructuredArrow.mkPrecomp (S := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorSource A D P x) f r

end SerrePositivity.InfinityCategories.Project.DerivedCategories
