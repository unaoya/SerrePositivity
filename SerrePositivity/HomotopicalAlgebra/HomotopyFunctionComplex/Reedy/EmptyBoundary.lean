module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.IndexReedy
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.RelativeArrow
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-! # Relative arrows at empty boundaries

At an empty latching or matching index the relative arrow is isomorphic
to the actual component. This applies to every diagram transformation.
-/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J)
  {C : Type u'} [Category.{v'} C] {F G : J ⥤ C} (τ : F ⟶ G)

instance matchingReedy_latching_isEmpty (g : MatchingIndex r j) :
    IsEmpty (LatchingIndex (matchingReedy r j) g) :=
  ⟨fun f ↦ f.property.2 f.property.1⟩

instance latchingReedy_matching_isEmpty (g : LatchingIndex r j) :
    IsEmpty (MatchingIndex (latchingReedy r j) g) :=
  ⟨fun f ↦ f.property.2 f.property.1⟩

section Latching
variable [IsEmpty (LatchingIndex r j)] [HasColimitsOfShape (LatchingIndex r j) C]
  [HasPushouts C]

instance latchingEvaluation_map_isIso_of_isEmpty : IsIso ((latchingEvaluation r j).map τ) := by
  have : ∀ x : LatchingIndex r j,
      IsIso ((Functor.whiskerLeft (latchingSource r j) τ).app x) := fun x ↦ isEmptyElim x
  have : IsIso (Functor.whiskerLeft (latchingSource r j) τ) := NatIso.isIso_of_isIso_app _
  change IsIso (colim.map (Functor.whiskerLeft (latchingSource r j) τ))
  infer_instance

def relativeLatchingEmptyIso : Arrow.mk (τ.app j) ≅ Arrow.mk (relativeLatchingMap r j τ) :=
  Arrow.isoMk (asIso (pushout.inr ((latchingEvaluation r j).map τ)
    ((latchingComparison r j).app F))) (Iso.refl _) (by
      simpa using inr_relativeLatchingMap r j τ)

end Latching

section Matching
variable [IsEmpty (MatchingIndex r j)] [HasLimitsOfShape (MatchingIndex r j) C]
  [HasPullbacks C]

instance matchingEvaluation_map_isIso_of_isEmpty : IsIso ((matchingEvaluation r j).map τ) := by
  have : ∀ x : MatchingIndex r j,
      IsIso ((Functor.whiskerLeft (matchingTarget r j) τ).app x) := fun x ↦ isEmptyElim x
  have : IsIso (Functor.whiskerLeft (matchingTarget r j) τ) := NatIso.isIso_of_isIso_app _
  change IsIso (lim.map (Functor.whiskerLeft (matchingTarget r j) τ))
  infer_instance

def relativeMatchingEmptyIso : Arrow.mk (relativeMatchingMap r j τ) ≅ Arrow.mk (τ.app j) :=
  Arrow.isoMk (Iso.refl _) (asIso (pullback.fst ((matchingComparison r j).app G)
    ((matchingEvaluation r j).map τ))) (by
      simpa using (relativeMatchingMap_fst r j τ).symm)

end Matching
end SerrePositivity.Reedy
