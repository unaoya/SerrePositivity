module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatSimplicial

/-!
概要：quasicategory の自己豊穣の前後合成は、元の内部 Hom の前後合成そのもの。
方針：閉構造の通常の射の curry と豊穣合成の公式を使う。
規約：core に移す前の全関手空間の作用を保持する。
使われ方：全高次の豊穣自然性を、元のパラメーター付き関手の自然性へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 元の自己豊穣の後合成は、同じ内部 Hom への実際の後合成。 -/
lemma quasicategoryHomWhiskerLeft (X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u})
    {Y Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u}} (f : Y ⟶ Z) :
    eHomWhiskerLeft SSet.{u} X f = (ihom X.obj).map f := by
  change (ρ_ ((ihom X.obj).obj Y.obj)).inv ≫
    _ ◁ curry' f ≫ MonoidalClosed.comp X.obj Y.obj Z.obj = _
  rw [whiskerLeft_curry'_comp, Iso.inv_hom_id_assoc]

/-- 元の自己豊穣の前合成は、同じ内部 Hom への実際の前合成。 -/
lemma quasicategoryHomWhiskerRight {X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u}}
    (f : X ⟶ Y) (Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u}) :
    eHomWhiskerRight SSet.{u} f Z =
      (pre (show X.obj ⟶ Y.obj from f)).app Z.obj := by
  change (λ_ ((ihom Y.obj).obj Z.obj)).inv ≫
    curry' (show X.obj ⟶ Y.obj from f) ▷ _ ≫ MonoidalClosed.comp X.obj Y.obj Z.obj = _
  rw [curry'_whiskerRight_comp, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
