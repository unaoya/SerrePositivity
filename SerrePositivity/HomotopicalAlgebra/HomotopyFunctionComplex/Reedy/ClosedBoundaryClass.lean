module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryClasses
public import SerrePositivity.HomotopicalAlgebra.Smith.ClosedGeneratedClass

/-! # Latching evaluation in a closed class without a global WFS

Generate a lifting class from just the small family of lower relative
latching maps. Its small-object argument is enough to reuse the proved
boundary lifting theorem. The global class need not be accessible.
-/

@[expose] public section
universe w v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ) (j : J)
  {C : Type u'} [Category.{v'} C] [HasFiniteLimits C] [HasFiniteColimits C]
  [IsLocallyPresentable.{w} C]
  [∀ k, HasColimitsOfShape (LatchingIndex r k) C]
  [Small.{w} (LatchingIndex r j)]
  {F G : J ⥤ C} (τ : F ⟶ G) (P : MorphismProperty C)
  [P.IsStableUnderRetracts] [P.IsStableUnderCoproducts.{w}]
  [P.IsStableUnderCobaseChange] [P.IsStableUnderTransfiniteComposition.{w}]

lemma latchingEvaluation_mem_closed
    (hτ : ∀ g : LatchingIndex r j, P (relativeLatchingMap r g.obj.left τ)) :
    P ((latchingEvaluation r j).map τ) := by
  let H := MorphismProperty.ofHoms
    (fun g : LatchingIndex r j => relativeLatchingMap r g.obj.left τ)
  have : H.IsSmall.{w} := inferInstanceAs (MorphismProperty.ofHoms _).IsSmall
  have := Smith.hasSmallObjectArgument H
  have hH : H ≤ P := by
    rintro X Y f ⟨g⟩
    exact hτ g
  have he := Smith.generatedLeft_le_of_closed H P hH
  apply he
  exact latchingEvaluation_mem_left r j τ H.rlp.llp H.rlp
    (fun g => H.le_llp_rlp _ (MorphismProperty.ofHoms.mk g))

end SerrePositivity.Reedy
