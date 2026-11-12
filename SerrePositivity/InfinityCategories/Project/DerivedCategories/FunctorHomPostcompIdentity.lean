module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomTypedWhiskerAlgebra
/-!
概要：指定余単位と完全充満性による元の入力比較の、任意全関手射自然性。
方針：全関手空間の交換則から同じ指定比較の正方形を得て、忠実性で反映する。
規約：比較を選び直さず、射の可逆性を要求しない。使われ方：分解変更の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
lemma functorHom_postcomp_id {X Y : SSet.{u}} {f g : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f g (𝟙 Y) e = e := by
  have hf : SSet.mapHomotopyCategory ((ihom X).map (𝟙 Y)) =
      𝟭 (SSet.HomotopyCategory ((ihom X).obj Y)) := by
    change (hoFunctor.map ((ihom X).map (𝟙 Y))).toFunctor = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  exact eq_of_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorMapHom_heq_of_functor_eq hf e)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
