module
public import SerrePositivity.KST.SConstruction.BundledDGInput
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGActionUnit
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGActionComposition

/-! # ラベル付き Perf の厳密 dg 入力に関する通常の関手
概要：ラベル付き dg 作用を、厳密な恒等・合成法則を持つ通常の関手に束ねる。
方針：元の全 Hom の作用と証明済みの dg 関手の等号を使う。
規約：高次入力の単体的豊穣は別工程。使われ方：厳密豊穣 Perf 関手の零単体部分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 小さい厳密 dg 入力から、全 Hom を保つラベル付き Perf への通常の関手。 -/
def presentedPerfectDGFunctor :
    SmallBundledDGCategory.{u, v} A ⥤ BundledDGCategory.{u, max (u + 1) v} A where
  obj C := bundledDGCategoryOf A (PresentedPerfectDGObject A C)
  map {C D} F := presentedPerfectDGAction A C D F
  map_id C := presentedPerfectDGAction_id A C
  map_comp {C D E} F G := (presentedPerfectDGAction_comp A C D E F G).symm

/-- 関手の対象は、元のラベル付き Perf dg 模型そのもの。 -/
lemma presentedPerfectDGFunctor_obj (C : SmallBundledDGCategory.{u, v} A) :
    (presentedPerfectDGFunctor A).obj C =
      bundledDGCategoryOf A (PresentedPerfectDGObject A C) := rfl

/-- 関手の射は、元の全 Hom 共役による dg 作用を変更せず回収する。 -/
lemma presentedPerfectDGFunctor_map {C D : SmallBundledDGCategory.{u, v} A} (F : C ⟶ D) :
    (presentedPerfectDGFunctor A).map F = presentedPerfectDGAction A C D F := rfl

end SerrePositivity.KST.SConstruction
