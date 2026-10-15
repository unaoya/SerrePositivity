module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryClasses
public import Mathlib.AlgebraicTopology.ModelCategory.Basic

/-! # Relative trivial Reedy maps and objectwise weak equivalences

Boundary evaluation preserves the relevant source lifting class. Strong
degree induction then identifies relative trivial maps with relative
cofibrations/fibrations which are objectwise weak equivalences.
-/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ)
  {C : Type u'} [Category.{v'} C] [ModelCategory C]
  {F G : J ⥤ C} (τ : F ⟶ G)

section Matching
variable [∀ j, HasLimitsOfShape (MatchingIndex r j) C]

lemma trivialFibration_app (hτ : reedyRight r (trivialFibrations C) τ) (j : J) :
    trivialFibrations C (τ.app j) := by
  have hM := matchingEvaluation_mem_right r j τ (cofibrations C) (trivialFibrations C)
    (fun g ↦ hτ g.obj.right)
  have hp := (trivialFibrations C).pullback_fst ((matchingComparison r j).app G)
    ((matchingEvaluation r j).map τ) hM
  have hc := (trivialFibrations C).comp_mem _ _ (hτ j) hp
  exact (relativeMatchingMap_fst r j τ) ▸ hc

lemma reedyRight_trivialFibrations_iff : reedyRight r (trivialFibrations C) τ ↔
    reedyRight r (fibrations C) τ ∧ ∀ j, weakEquivalences C (τ.app j) := by
  constructor
  · intro hτ
    exact ⟨fun j ↦ (hτ j).1, fun j ↦ (trivialFibration_app r τ hτ j).2⟩
  · rintro ⟨hτ, hw⟩ j
    have h : ∀ n (j : J), r.deg j = n → trivialFibrations C (relativeMatchingMap r j τ) := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro j hj
        have hM := matchingEvaluation_mem_right r j τ (cofibrations C) (trivialFibrations C)
          (fun g ↦ ih (r.deg g.obj.right) (hj ▸ matching_degree_lt r g) g.obj.right rfl)
        have hp := (trivialFibrations C).pullback_fst ((matchingComparison r j).app G)
          ((matchingEvaluation r j).map τ) hM
        refine ⟨hτ j, (weakEquivalences C).of_postcomp _ _ hp.2 ?_⟩
        exact (relativeMatchingMap_fst r j τ).symm ▸ hw j
    exact h (r.deg j) j rfl

end Matching

section Latching
variable [∀ j, HasColimitsOfShape (LatchingIndex r j) C]

lemma trivialCofibration_app (hτ : reedyLeft r (trivialCofibrations C) τ) (j : J) :
    trivialCofibrations C (τ.app j) := by
  have hL := latchingEvaluation_mem_left r j τ (trivialCofibrations C) (fibrations C)
    (fun g ↦ hτ g.obj.left)
  have hi := (trivialCofibrations C).pushout_inr ((latchingEvaluation r j).map τ)
    ((latchingComparison r j).app F) hL
  have hc := (trivialCofibrations C).comp_mem _ _ hi (hτ j)
  exact (inr_relativeLatchingMap r j τ) ▸ hc

lemma reedyLeft_trivialCofibrations_iff : reedyLeft r (trivialCofibrations C) τ ↔
    reedyLeft r (cofibrations C) τ ∧ ∀ j, weakEquivalences C (τ.app j) := by
  constructor
  · intro hτ
    exact ⟨fun j ↦ (hτ j).1, fun j ↦ (trivialCofibration_app r τ hτ j).2⟩
  · rintro ⟨hτ, hw⟩ j
    have h : ∀ n (j : J), r.deg j = n → trivialCofibrations C (relativeLatchingMap r j τ) := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro j hj
        have hL := latchingEvaluation_mem_left r j τ (trivialCofibrations C) (fibrations C)
          (fun g ↦ ih (r.deg g.obj.left) (hj ▸ latching_degree_lt r g) g.obj.left rfl)
        have hi := (trivialCofibrations C).pushout_inr ((latchingEvaluation r j).map τ)
          ((latchingComparison r j).app F) hL
        refine ⟨hτ j, (weakEquivalences C).of_precomp _ _ hi.2 ?_⟩
        exact (inr_relativeLatchingMap r j τ).symm ▸ hw j
    exact h (r.deg j) j rfl

end Latching
end SerrePositivity.Reedy
