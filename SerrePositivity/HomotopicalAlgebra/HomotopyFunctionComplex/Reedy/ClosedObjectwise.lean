module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ClosedBoundaryClass

/-! # Reedy relative classes from objectwise equivalences in a closed class

Only the closure properties of L ∩ W and two-out-of-three for W are used.
In particular there is no model structure with W as weak equivalences.
-/

@[expose] public section
universe w v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ)
  {C : Type u'} [Category.{v'} C] [HasFiniteLimits C] [HasFiniteColimits C]
  [IsLocallyPresentable.{w} C]
  [∀ j, HasColimitsOfShape (LatchingIndex r j) C]
  [∀ j, Small.{w} (LatchingIndex r j)]
  {F G : J ⥤ C} (τ : F ⟶ G)

lemma app_mem_closed (P : MorphismProperty C) [P.IsMultiplicative]
    [P.IsStableUnderRetracts] [P.IsStableUnderCoproducts.{w}]
    [P.IsStableUnderCobaseChange] [P.IsStableUnderTransfiniteComposition.{w}]
    (hτ : reedyLeft r P τ) (j : J) : P (τ.app j) := by
  have hL := latchingEvaluation_mem_closed r j τ P (fun g => hτ g.obj.left)
  have hi := P.pushout_inr ((latchingEvaluation r j).map τ) ((latchingComparison r j).app F) hL
  exact (inr_relativeLatchingMap r j τ) ▸ P.comp_mem _ _ hi (hτ j)

lemma reedyLeft_inf_iff (L W : MorphismProperty C) [W.HasTwoOutOfThreeProperty]
    [(L ⊓ W).IsMultiplicative] [(L ⊓ W).IsStableUnderRetracts]
    [(L ⊓ W).IsStableUnderCoproducts.{w}] [(L ⊓ W).IsStableUnderCobaseChange]
    [(L ⊓ W).IsStableUnderTransfiniteComposition.{w}] :
    reedyLeft r (L ⊓ W) τ ↔ reedyLeft r L τ ∧ ∀ j, W (τ.app j) := by
  constructor
  · intro hτ
    exact ⟨fun j => (hτ j).1, fun j => (app_mem_closed r τ (L ⊓ W) hτ j).2⟩
  · rintro ⟨hτ, hw⟩ j
    have h : ∀ n (j : J), r.deg j = n → (L ⊓ W) (relativeLatchingMap r j τ) := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro j hj
        have hL := latchingEvaluation_mem_closed r j τ (L ⊓ W)
          (fun g => ih (r.deg g.obj.left) (hj ▸ latching_degree_lt r g) g.obj.left rfl)
        have hi := (L ⊓ W).pushout_inr ((latchingEvaluation r j).map τ)
          ((latchingComparison r j).app F) hL
        exact ⟨hτ j, W.of_precomp _ _ hi.2 ((inr_relativeLatchingMap r j τ).symm ▸ hw j)⟩
    exact h (r.deg j) j rfl

end SerrePositivity.Reedy
