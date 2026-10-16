module

public import SerrePositivity.CategoryTheory.Presentation.RetractWords
public import SerrePositivity.CategoryTheory.Quiver.PathFunctorExt

/-! # Extensionality on the actual generating arrows of the retract-word quotient -/

@[expose] public section
universe u v w uD vD
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.RetractWords
variable {C : Type u} [Category.{v} C] {M : Type w} [MonoidWithZero M]
  {D : Type uD} [Category.{vD} D]

lemma functor_ext_generators (F G : Obj C M ⥤ D) (ho : ∀ X, F.obj X = G.obj X)
    (hm : ∀ {X Y : Vertex C M} (e : X ⟶ Y),
      HEq (F.map ((quotient C M).map ((Paths.of _).map e)))
        (G.map ((quotient C M).map ((Paths.of _).map e)))) : F = G := by
  apply CategoryTheory.Quotient.lift_unique' (Rel C M)
  apply QuiverPaths.functor_ext_edges
  · intro X
    exact ho ((quotient C M).obj X)
  · intro X Y e
    exact hm e

end SerrePositivity.RetractWords
