module
public import SerrePositivity.KST.SConstruction.DGGluingAxesRepresentableCofiber

/-! # 実四代表 cofiber の元の四辺と対角
概要：実代表加群四角形の各閉射を、元の二軸射と零射の Yoneda 像へ照合する。
方針：元の円錐比較の包含回収と零角変更の定義を使う。
規約：全二セルの比較に使う厳密な等式。使われ方：元の dg nerve の四角形の持ち上げ。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (zc : C) (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (zd : D) (hd : IsZero (ForgetEnrichment.of (Complex R) zd))
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "A" => ForgetEnrichment.of (Complex R)
  (dgGluingRightAxisObject R C D M zc X.right)
local notation "B" => ForgetEnrichment.of (Complex R)
  (dgGluingLeftAxisObject R C D M zd X.left)
local notation "Z" => ForgetEnrichment.of (Complex R)
  (dgGluingRightAxisObject R C D M zc zd)
local notation "s" => dgGluingAxesRepresentableCofiberData R C D M zc hc zd hd X
local notation "F" => DGFunctor.onClosed (dgYoneda R G)

/-- 元の実四代表四角形の下射は、元の右軸包含の Yoneda 像。 -/
lemma dgGluingAxesRepresentable_bottom :
    (s).bottom = (F).map (dgGluingAxisRightInclusion R C D M zc hc X) := rfl

/-- 元の実四代表四角形の右射は、元の左軸射影の Yoneda 像。 -/
lemma dgGluingAxesRepresentable_right :
    (s).right = (F).map (dgGluingAxisLeftProjection R C D M zd hd X) :=
  dgGluingAxesYonedaCofiberData_right R C D M zc hc zd hd X

/-- 元の実四代表四角形の左射は、指定零対象への零射の Yoneda 像。 -/
lemma dgGluingAxesRepresentable_left : (s).left = (F).map (0 : A ⟶ Z) := by
  change (0 : (F).obj A ⟶ moduleZero R G) ≫ 0 = (F).map (0 : A ⟶ Z)
  exact (zero_comp).trans ((F).map_zero A Z).symm

/-- 元の実四代表四角形の上射は、指定零対象からの零射の Yoneda 像。 -/
lemma dgGluingAxesRepresentable_top : (s).top = (F).map (0 : Z ⟶ B) :=
  ((F).map_zero Z B).symm

/-- 元の実四代表四角形の対角は、元の右軸から左軸への零射の Yoneda 像。 -/
lemma dgGluingAxesRepresentable_diagonal : (s).diagonal = (F).map (0 : A ⟶ B) := by
  change (0 : (F).obj A ⟶ moduleCone R G
    (dgGluingAxesYonedaRightMap R C D M zc hc X)) ≫
      dgGluingAxesYonedaConeComparison R C D M zc hc zd hd X = (F).map (0 : A ⟶ B)
  exact (zero_comp).trans ((F).map_zero A B).symm

end SerrePositivity.KST.SConstruction
