module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：元の三角形の族を指定射で後合成し、元の三円柱の像を三辺として保持する。
方針：内部 Hom の map で元の全二単体を写す。
規約：辺を選び直さない。使われ方：部分極限比較の三角形の頂点評価。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 元の比較三角形の全パラメータを、そのまま指定射で後合成する。 -/
def postcomposeFunctorCompositionTriangle {A X Y : SSet.{u}} (p : X ⟶ Y)
    {f g h : A ⟶ X} {l : SSet.Homotopy f g} {r : SSet.Homotopy g h}
    {d : SSet.Homotopy f h} (T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp l p)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp r p) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp d p) where
  diagram := T.diagram ≫ (ihom A).map p
  face_zero := by
    rw [← Category.assoc, T.face_zero]
    apply uncurry_injective
    rw [uncurry_natural_right, uncurry_curry, uncurry_curry]
    rfl
  face_one := by
    rw [← Category.assoc, T.face_one]
    apply uncurry_injective
    rw [uncurry_natural_right, uncurry_curry, uncurry_curry]
    rfl
  face_two := by
    rw [← Category.assoc, T.face_two]
    apply uncurry_injective
    rw [uncurry_natural_right, uncurry_curry, uncurry_curry]
    rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
