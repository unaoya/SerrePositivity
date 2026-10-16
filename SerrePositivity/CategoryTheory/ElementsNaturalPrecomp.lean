module

public import Mathlib.CategoryTheory.Elements

/-! # The actual category-of-elements comparison along a natural transformation

The original elements and all base maps are retained. No faithfulness of
the element projection or smallness of the index category is required.
-/

@[expose] public section
universe vC uC vI uI w
noncomputable section
open CategoryTheory

namespace SerrePositivity.ElementsNaturalPrecomp
variable {C : Type uC} [Category.{vC} C] {I : Type uI} [Category.{vI} I]
  (F : C ⥤ Type w) {P Q : I ⥤ C} (α : P ⟶ Q)

def comparison : Functor.Elements.precomp P F ⟶
    (Functor.whiskerRight α F).mapElements ⋙ Functor.Elements.precomp Q F where
  app e := Functor.Elements.homMk (α.app e.obj) rfl
  naturality {e e'} f := by
    apply Functor.Elements.hom_ext
    exact α.naturality f.hom

lemma comparison_hom (e : (P ⋙ F).Elements) :
    ((comparison F α).app e).hom = α.app e.obj := rfl

end SerrePositivity.ElementsNaturalPrecomp
