module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FactorizationClasses
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Lifting
public import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem

/-! # Lifting weak factorization systems to Reedy diagram categories

For the natural-number degree bijections needed for Δ and Δop, an ordinary
weak factorization system in the value category yields a weak factorization
system defined by relative latching and relative matching arrows. The proof
uses the constructed global factors, retract closure, and the global Reedy
lifting theorem. No functorial source factorization is assumed.
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
  (left right : MorphismProperty C) [MorphismProperty.IsWeakFactorizationSystem left right]

lemma lifting_of_reedy {A B X Y : J ⥤ C} (i : A ⟶ B) (p : X ⟶ Y)
    (hi : reedyLeft r left i) (hp : reedyRight r right p) : HasLiftingProperty i p := by
  let : ∀ j, HasLiftingProperty (relativeLatchingMap r j i) (relativeMatchingMap r j p) :=
    fun j ↦ MorphismProperty.hasLiftingProperty_of_wfs _ _ (hi j) (hp j)
  exact Lifting.hasLiftingProperty r

lemma weakFactorizationSystem (hinj : Function.Injective r.deg)
    (hsurj : Function.Surjective r.deg) :
    MorphismProperty.IsWeakFactorizationSystem (reedyLeft r left) (reedyRight r right) := by
  let : left.IsStableUnderRetracts := by
    rw [← MorphismProperty.llp_eq_of_wfs left right]
    infer_instance
  let : right.IsStableUnderRetracts := by
    rw [← MorphismProperty.rlp_eq_of_wfs left right]
    infer_instance
  let : (reedyLeft r left).HasFactorization (reedyRight r right) :=
    { nonempty_mapFactorizationData τ :=
        ⟨FactorizationSequence.reedyOfHasFactorization r τ hinj hsurj⟩ }
  exact MorphismProperty.IsWeakFactorizationSystem.mk' _ _
    (fun i p hi hp ↦ lifting_of_reedy r left right i p hi hp)

end SerrePositivity.Reedy
