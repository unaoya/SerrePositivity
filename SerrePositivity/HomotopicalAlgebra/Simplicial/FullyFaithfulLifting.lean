module

public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! # Lifting properties under fully faithful functors

Both arrows are in the image. Fullness transports the boundary of every
square, and faithfulness transports its commutativity and lift equations.
No adjoint or model structure is required.
-/

@[expose] public section
universe u v u' v'
noncomputable section
open CategoryTheory

namespace SerrePositivity.ModelGeneration
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) [F.Full] [F.Faithful]

lemma hasLiftingProperty_map_iff {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) :
    HasLiftingProperty (F.map i) (F.map p) ↔ HasLiftingProperty i p := by
  constructor
  · intro h
    constructor
    intro f g sq
    have sq' := sq.map F
    exact CommSq.HasLift.mk'
      { l := F.preimage sq'.lift
        fac_left := F.map_injective (by
          simpa only [Functor.map_comp, Functor.map_preimage] using sq'.fac_left)
        fac_right := F.map_injective (by
          simpa only [Functor.map_comp, Functor.map_preimage] using sq'.fac_right) }
  · intro h
    constructor
    intro f g sq
    have sq' : CommSq (F.preimage f) i p (F.preimage g) := ⟨F.map_injective (by
      simpa only [Functor.map_comp, Functor.map_preimage] using sq.w)⟩
    exact CommSq.HasLift.mk'
      { l := F.map sq'.lift
        fac_left := by
          simpa only [Functor.map_comp, Functor.map_preimage] using congrArg F.map sq'.fac_left
        fac_right := by
          simpa only [Functor.map_comp, Functor.map_preimage] using congrArg F.map sq'.fac_right }

end SerrePositivity.ModelGeneration
