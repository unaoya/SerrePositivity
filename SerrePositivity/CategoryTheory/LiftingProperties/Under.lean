module

public import Mathlib.CategoryTheory.LiftingProperties.Over

/-!
# Lifting properties in under categories

Dual of the Over construction in the pinned Mathlib
`CategoryTheory/LiftingProperties/Over.lean` (Joël Riou, Apache 2.0).
-/

@[expose] public section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {S : C}

/-- A lift of the underlying square gives a lift in `Under S`. -/
lemma CommSq.HasLift.under {X₁ X₂ X₃ X₄ : Under S}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    {sq : CommSq t l r b}
    [CommSq.HasLift (f := t.right) (i := l.right) (p := r.right) (g := b.right)
      (sq.map (Under.forget S))] : sq.HasLift := by
  let sq' := sq.map (Under.forget S)
  dsimp at sq'
  exact ⟨⟨{
    l := Under.homMk sq'.lift
      (by rw [← Under.w l, Category.assoc, sq'.fac_left, Under.w t])
  }⟩⟩

/-- An underlying lifting property suffices for the lifting property in
the under category. It is not asserted to be necessary. -/
lemma HasLiftingProperty.under {A B X Y : Under S} (i : A ⟶ B) (p : X ⟶ Y)
    [HasLiftingProperty i.right p.right] : HasLiftingProperty i p :=
  ⟨fun _ ↦ .under⟩

end CategoryTheory
