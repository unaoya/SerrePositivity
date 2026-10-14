module

public import SerrePositivity.CategoryTheory.FiniteBijectionShift
public import SerrePositivity.CategoryTheory.Groupoid.ThinComponents
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-! # Freeness of finite-bijection induction indices

Adding a fixed right block is faithful. Its costructured arrows over a finite
set form a thin groupoid, so colimits over these indices preserve morphism
properties stable under coproducts.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.FiniteBijection

instance addRight_faithful (n : ℕ) : (addRight n).Faithful where
  map_injective {A B} f g h := by
    apply (homEquiv A B).injective
    apply Equiv.ext
    intro i
    have he : blockEquiv (equivOfHom f) (Equiv.refl (Fin n)) =
        blockEquiv (equivOfHom g) (Equiv.refl (Fin n)) := by
      simpa [addRight, sumMap, sumObj, card, of, FintypeCat.Skeleton.mk,
        FintypeCat.Skeleton.len] using congrArg equivOfHom h
    have hh := congrArg (fun e ↦ e (finSumFinEquiv (Sum.inl i))) he
    have hh' := congrArg
      (fun x ↦ (finSumFinEquiv : Fin (card B) ⊕ Fin n ≃ Fin (card B + n)).symm x) hh
    change equivOfHom f i = equivOfHom g i
    simpa [blockEquiv] using hh'

/-- All induction-index morphisms are invertible; the underlying finite
bijection supplies the inverse and its commuting triangle. -/
instance induction_isGroupoid (n m : ℕ) :
    IsGroupoid (CostructuredArrow (addRight n) (of m)) where
  all_isIso {A B} f := by
    let e : A ≅ B := CostructuredArrow.isoMk (asIso f.left) (CostructuredArrow.w f)
    have he : e.hom = f := CostructuredArrow.hom_ext _ _ rfl
    rw [← he]
    infer_instance

/-- The commuting triangle determines its left bijection uniquely. -/
instance induction_isThin (n m : ℕ) :
    Quiver.IsThin (CostructuredArrow (addRight n) (of m)) := by
  intro A B
  constructor
  intro f g
  apply CostructuredArrow.hom_ext
  apply (addRight n).map_injective
  apply (cancel_mono B.hom).1
  exact (CostructuredArrow.w f).trans (CostructuredArrow.w g).symm

end SerrePositivity.FiniteBijection
