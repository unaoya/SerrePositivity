module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.EmptyBoundary
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Lifting
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction
public import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem

/-! # Lifting classes under inverse limits and direct colimits

The result uses the constructed global Reedy lifting theorem and the
constant/limit or colimit/constant adjunction. The one-sided condition is
expressed by empty opposite boundaries and does not require injective degrees.
-/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ) {C : Type u'} [Category.{v'} C]
  [∀ j, HasColimitsOfShape (LatchingIndex r j) C]
  [∀ j, HasLimitsOfShape (MatchingIndex r j) C] [HasPushouts C] [HasPullbacks C]
  {F G : J ⥤ C} (τ : F ⟶ G)

section Limit
variable [∀ j, IsEmpty (LatchingIndex r j)] [HasLimitsOfShape J C]

include r in
lemma hasLiftingProperty_limit {A B : C} (i : A ⟶ B)
    [∀ j, HasLiftingProperty i (relativeMatchingMap r j τ)] :
    HasLiftingProperty i (lim.map τ) := by
  have : ∀ j, HasLiftingProperty
      (relativeLatchingMap r j ((Functor.const J).map i)) (relativeMatchingMap r j τ) := fun j ↦ by
    have : HasLiftingProperty (((Functor.const J).map i).app j) (relativeMatchingMap r j τ) :=
      inferInstanceAs (HasLiftingProperty i (relativeMatchingMap r j τ))
    exact HasLiftingProperty.of_arrow_iso_left
      (relativeLatchingEmptyIso r j ((Functor.const J).map i)) _
  have : HasLiftingProperty ((Functor.const J).map i) τ := Lifting.hasLiftingProperty r
  exact (constLimAdj.hasLiftingProperty_iff i τ).mp this

lemma limit_mem_right (left right : MorphismProperty C)
    [MorphismProperty.IsWeakFactorizationSystem left right] (hτ : reedyRight r right τ) :
    right (lim.map τ) := by
  rw [← MorphismProperty.rlp_eq_of_wfs left right]
  intro A B i hi
  have : ∀ j, HasLiftingProperty i (relativeMatchingMap r j τ) := fun j ↦
    MorphismProperty.hasLiftingProperty_of_wfs i _ hi (hτ j)
  exact hasLiftingProperty_limit r τ i

end Limit

section Colimit
variable [∀ j, IsEmpty (MatchingIndex r j)] [HasColimitsOfShape J C]

include r in
lemma hasLiftingProperty_colimit {X Y : C} (p : X ⟶ Y)
    [∀ j, HasLiftingProperty (relativeLatchingMap r j τ) p] :
    HasLiftingProperty (colim.map τ) p := by
  have : ∀ j, HasLiftingProperty (relativeLatchingMap r j τ)
      (relativeMatchingMap r j ((Functor.const J).map p)) := fun j ↦ by
    have : HasLiftingProperty (relativeLatchingMap r j τ) (((Functor.const J).map p).app j) :=
      inferInstanceAs (HasLiftingProperty (relativeLatchingMap r j τ) p)
    exact HasLiftingProperty.of_arrow_iso_right _
      (relativeMatchingEmptyIso r j ((Functor.const J).map p)).symm
  have : HasLiftingProperty τ ((Functor.const J).map p) := Lifting.hasLiftingProperty r
  exact (colimConstAdj.hasLiftingProperty_iff τ p).mpr this

lemma colimit_mem_left (left right : MorphismProperty C)
    [MorphismProperty.IsWeakFactorizationSystem left right] (hτ : reedyLeft r left τ) :
    left (colim.map τ) := by
  rw [← MorphismProperty.llp_eq_of_wfs left right]
  intro X Y p hp
  have : ∀ j, HasLiftingProperty (relativeLatchingMap r j τ) p := fun j ↦
    MorphismProperty.hasLiftingProperty_of_wfs _ p (hτ j) hp
  exact hasLiftingProperty_colimit r τ p

end Colimit
end SerrePositivity.Reedy
