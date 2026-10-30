module

public import Mathlib.CategoryTheory.NatIso

/-! # A reflection criterion for a coaugmented functor

The comparison between the functor applied to its unit and the unit at its image
must be proved separately for a concrete completion functor.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe v u
namespace SerrePositivity
open CategoryTheory
variable {C : Type u} [Category.{v} C] (L : C ⥤ C) (η : 𝟭 C ⟶ L)

/-- Invertibility of both iterated units forces their equality. -/
theorem coaugmentedUnit_comm_of_isIso
    (hη : ∀ X, IsIso (η.app (L.obj X)))
    (hLη : ∀ X, IsIso (L.map (η.app X))) (X : C) :
    L.map (η.app X) = η.app (L.obj X) := by
  let := hη X
  let := hη (L.obj X)
  let := hLη X
  have h₁ : η.app (L.obj (L.obj X)) = L.map (η.app (L.obj X)) := by
    apply (cancel_epi (η.app (L.obj X))).mp
    exact η.naturality (η.app (L.obj X))
  have h₂ : L.map (η.app (L.obj X)) = L.map (L.map (η.app X)) := by
    apply (cancel_epi (L.map (η.app X))).mp
    simpa only [Functor.id_map, Functor.id_obj, ← L.map_comp] using
      congrArg (fun f ↦ L.map f) (η.naturality (η.app X))
  apply (cancel_mono (η.app (L.obj (L.obj X)))).mp
  calc
    _ = η.app (L.obj X) ≫ L.map (L.map (η.app X)) := by
      simpa only [Functor.id_map, Functor.id_obj] using η.naturality (L.map (η.app X))
    _ = _ := by rw [← h₂, ← h₁]

/-- The universal extension to a fixed target of the coaugmentation. -/
def coaugmentedHomEquiv
    (hcomm : ∀ X, L.map (η.app X) = η.app (L.obj X))
    (X Y : C) [IsIso (η.app Y)] :
    (L.obj X ⟶ Y) ≃ (X ⟶ Y) where
  toFun f := η.app X ≫ f
  invFun f := L.map f ≫ inv (η.app Y)
  left_inv f := by
    change L.map (η.app X ≫ f) ≫ inv (η.app Y) = f
    rw [L.map_comp, hcomm, ← η.naturality f]
    simp
  right_inv f := by
    change η.app X ≫ (L.map f ≫ inv (η.app Y)) = f
    rw [← Category.assoc, ← η.naturality f]
    simp

@[simp] theorem coaugmentedHomEquiv_apply
    (hcomm : ∀ X, L.map (η.app X) = η.app (L.obj X))
    (X Y : C) [IsIso (η.app Y)] (f : L.obj X ⟶ Y) :
    coaugmentedHomEquiv L η hcomm X Y f = η.app X ≫ f := rfl

@[simp] theorem coaugmentedHomEquiv_symm_apply
    (hcomm : ∀ X, L.map (η.app X) = η.app (L.obj X))
    (X Y : C) [IsIso (η.app Y)] (f : X ⟶ Y) :
    (coaugmentedHomEquiv L η hcomm X Y).symm f = L.map f ≫ inv (η.app Y) := rfl

end SerrePositivity
