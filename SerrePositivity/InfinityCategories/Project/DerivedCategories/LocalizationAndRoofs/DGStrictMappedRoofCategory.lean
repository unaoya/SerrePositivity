module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGStrictRoofCategory

/-! # dg 関手で写した始域からの閉分子を持つ厳密屋根

概要：元の閉実分母と、その始域の dg 関手像からの閉分子を持つ屋根を圏にする。
方針：閉分母の始域関手と dg 関手の閉零関手の合成の costructured arrow を取る。
規約：閉分母は元の dg 圏のまま。使われ方：商側の任意の閉分子の実屋根への表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D E : Type v) [DGCategory A D] [DGCategory A E]
variable (F : DGFunctor A D E)

/-- 元の閉実分母と、その始域の像からの閉分子を持つ厳密屋根の圏。 -/
abbrev DGStrictMappedRoofs (P : Set D) (x : D) (y : E) :=
  CostructuredArrow (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorSource A D P x ⋙ F.onClosed)
    (ForgetEnrichment.of (Complex A) y)

/-- 写した閉分子を持つ厳密屋根から、元の閉分母への射影。 -/
def dgStrictMappedRoofDenominator (P : Set D) (x : D) (y : E) :
    DGStrictMappedRoofs A D E F P x y ⥤ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x :=
  CostructuredArrow.proj _ _

/-- 写した閉分子を、像の圏の固定終点の通常の over 対象として読む。 -/
def dgStrictMappedRoofNumerator (P : Set D) (x : D) (y : E) :
    DGStrictMappedRoofs A D E F P x y ⥤ Over (ForgetEnrichment.of (Complex A) y) where
  obj s := Over.mk s.hom
  map r := Over.homMk ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorSource A D P x ⋙ F.onClosed).map r.left)
    (CostructuredArrow.w r)

/-- 指定元の閉分母と写した始域の閉分子は、同じ厳密屋根圏の対象を与える。 -/
def dgStrictMappedRoofMk (P : Set D) (x : D) (y : E)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x)
    (f : F.onClosed.obj s.obj.left ⟶ ForgetEnrichment.of (Complex A) y) :
    DGStrictMappedRoofs A D E F P x y :=
  CostructuredArrow.mk f

/-- 元の指定厳密細分射の像で閉分子を前合成し、同じ厳密屋根圏の射を得る。 -/
def dgStrictMappedRoofRefine (P : Set D) (x : D) (y : E)
    {s t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x} (r : s ⟶ t)
    (f : F.onClosed.obj t.obj.left ⟶ ForgetEnrichment.of (Complex A) y) :
    dgStrictMappedRoofMk A D E F P x y s (F.onClosed.map r.hom.left ≫ f) ⟶
      dgStrictMappedRoofMk A D E F P x y t f :=
  CostructuredArrow.mkPrecomp
    (S := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorSource A D P x ⋙ F.onClosed) f r

end SerrePositivity.InfinityCategories.Project.DerivedCategories
