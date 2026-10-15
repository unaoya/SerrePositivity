module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryClasses
public import Mathlib.AlgebraicTopology.ModelCategory.Basic

/-! # Components of Reedy cofibrations and fibrations -/

@[expose] public section
universe v u v' u'
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ) {C : Type u'} [Category.{v'} C] [ModelCategory C]
  {F G : J ⥤ C} (τ : F ⟶ G)

lemma cofibration_app [∀ j, HasColimitsOfShape (LatchingIndex r j) C]
    (hτ : reedyLeft r (cofibrations C) τ) (j : J) : cofibrations C (τ.app j) := by
  have hL := latchingEvaluation_mem_left r j τ (cofibrations C) (trivialFibrations C)
    (fun g ↦ hτ g.obj.left)
  have hi := (cofibrations C).pushout_inr ((latchingEvaluation r j).map τ)
    ((latchingComparison r j).app F) hL
  exact (inr_relativeLatchingMap r j τ) ▸ (cofibrations C).comp_mem _ _ hi (hτ j)

lemma fibration_app [∀ j, HasLimitsOfShape (MatchingIndex r j) C]
    (hτ : reedyRight r (fibrations C) τ) (j : J) : fibrations C (τ.app j) := by
  have hM := matchingEvaluation_mem_right r j τ (trivialCofibrations C) (fibrations C)
    (fun g ↦ hτ g.obj.right)
  have hp := (fibrations C).pullback_fst ((matchingComparison r j).app G)
    ((matchingEvaluation r j).map τ) hM
  exact (relativeMatchingMap_fst r j τ) ▸ (fibrations C).comp_mem _ _ (hτ j) hp

end SerrePositivity.Reedy
