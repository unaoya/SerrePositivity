module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DoubleMappingCylinderMap
public import SerrePositivity.KST.Comparison.CylinderBoundary
public import Mathlib.CategoryTheory.Adhesive.Basic

/-!
# 単射な脚の pushout の厳密な引き戻しの貼り合わせ

概要：単体集合の単射に沿う pushout の van Kampen 性から、厳密な引き戻しの貼り合わせを得る。
方針：Mathlib の型の adhesive 性と関手圏への移送を使う。
規約：Segal 1974 Lemma 1.7 の厳密な四角形の部分。homotopy-cartesian への移行は別項目。
使われ方：二重写像円筒の実際の pushout の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory
open scoped _root_.Simplicial

/--
概要：単射な脚を持つ単体集合の pushout の可換な立方体では、後ろ二面の引き戻しが前二面へ移る。
方針：単体集合の adhesive 性の van Kampen 条件を使う。
規約：全ての仮定は実際の pushout と pullback の四角形。
使われ方：二重写像円筒の厳密なファイバーの貼り合わせ。
-/
theorem strictPushoutCube {W X Y Z W' X' Y' Z' : SSet.{u}}
    {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    {f' : W' ⟶ X'} {g' : W' ⟶ Y'} {h' : X' ⟶ Z'} {i' : Y' ⟶ Z'}
    [Mono f] (sq : IsPushout f g h i) (sq' : IsPushout f' g' h' i')
    (aW : W' ⟶ W) (aX : X' ⟶ X) (aY : Y' ⟶ Y) (aZ : Z' ⟶ Z)
    (hf : IsPullback f' aW aX f) (hg : IsPullback g' aW aY g)
    (hh : CommSq h' aX aZ h) (hi : CommSq i' aY aZ i) :
    IsPullback h' aX aZ h ∧ IsPullback i' aY aZ i :=
  ((Adhesive.van_kampen sq) f' g' h' i' aW aX aY aZ hf hg hh hi sq'.toCommSq).mp sq'

/--
概要：二重写像円筒の pushout の厳密な引き戻しの立方体の前二面は引き戻しになる。
方針：中央の円筒と両端の余積の四角形へ、単射な貼り付けの van Kampen 性を使う。
規約：Segal Lemma 1.7 の厳密な版の実模型への接続。
使われ方：homotopy-cartesian な模型への移行のための厳密な比較。
-/
theorem doubleMappingCylinderMap_strictCube {C A B C' A' B' : SSet.{u}}
    (f : C ⟶ A) (g : C ⟶ B) (f' : C' ⟶ A') (g' : C' ⟶ B')
    (c : C ⟶ C') (a : A ⟶ A') (b : B ⟶ B')
    (hf : c ≫ f' = f ≫ a) (hg : c ≫ g' = g ≫ b)
    (h₁ : IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints C) (coprod.map c c) (c ▷ Δ[1]) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints C'))
    (h₂ : IsPullback (coprod.map f g) (coprod.map c c) (coprod.map a b) (coprod.map f' g')) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_middle f g) (c ▷ Δ[1])
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap f g f' g' c a b hf hg) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_middle f' g') ∧
    IsPullback (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints C) (coprod.map f g)) (coprod.map a b)
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap f g f' g' c a b hf hg)
        (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints C') (coprod.map f' g')) := by
  apply strictPushoutCube
    (IsPushout.of_hasPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints C') (coprod.map f' g'))
    (IsPushout.of_hasPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints C) (coprod.map f g))
    (coprod.map c c) (c ▷ Δ[1]) (coprod.map a b)
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap f g f' g' c a b hf hg) h₁ h₂
  · exact ⟨_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_middle_map f g f' g' c a b hf hg⟩
  · refine ⟨?_⟩
    apply coprod.hom_ext
    · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left, Category.assoc, coprod.inl_map_assoc] using
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_left_map f g f' g' c a b hf hg
    · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right, Category.assoc, coprod.inr_map_assoc] using
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_right_map f g f' g' c a b hf hg

end SerrePositivity.KST.Comparison
