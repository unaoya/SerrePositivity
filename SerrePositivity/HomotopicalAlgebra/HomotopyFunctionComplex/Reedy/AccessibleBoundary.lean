module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionBoundary
public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleLimits
public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleFamilies
public import SerrePositivity.HomotopicalAlgebra.Smith.Smallness
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Accessibility of the actual lower latching and matching evaluations

Latching evaluation preserves all colimits. Matching evaluation is accessible
by the proved right-adjoint theorem. A small family of degrees has a common
cardinal, although it need not be the original model-factorization cardinal.
-/

@[expose] public section
universe w v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ) {C : Type u'} [Category.{v'} C]

lemma lowerLatchingEvaluation_isCardinalAccessible (j : J)
    [HasColimitsOfShape (LatchingIndex r j) C]
    [HasColimitsOfSize.{w, w} C]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    (lowerLatchingEvaluation (C := C) r j).IsCardinalAccessible κ := by
  exact inferInstanceAs (Functor.IsCardinalAccessible
    ((Functor.whiskeringLeft _ _ C).obj (latchingSourceLower r j) ⋙ colim) κ)

lemma lowerMatchingEvaluation_isAccessible [IsLocallyPresentable.{w} C] [HasPullbacks C]
    (j : J) [EssentiallySmall.{w} (MatchingIndex r j)]
    [HasLimitsOfShape (MatchingIndex r j) C] :
    (lowerMatchingEvaluation (C := C) r j).IsAccessible.{w} := by
  have := Smith.locallyPresentable_hasColimits (C := C)
  have hlim := Smith.AccessibleLimits.limitFunctor_isAccessible (C := C) (MatchingIndex r j)
  let pre := (Functor.whiskeringLeft _ _ C).obj (matchingTargetLower r j)
  have : Fact Cardinal.aleph0.IsRegular := Cardinal.fact_isRegular_aleph0
  have : pre.IsAccessible.{w} :=
    pre.isAccessible_of_isCardinalAccessible Cardinal.aleph0
  exact inferInstanceAs ((pre ⋙ lim).IsAccessible.{w})

lemma exists_common_boundary_accessibility [IsLocallyPresentable.{w} C] [HasPullbacks C]
    [Small.{w} J] [∀ j, EssentiallySmall.{w} (MatchingIndex r j)]
    [∀ j, HasColimitsOfShape (LatchingIndex r j) C]
    [∀ j, HasLimitsOfShape (MatchingIndex r j) C] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular), ∀ j,
      (lowerLatchingEvaluation (C := C) r j).IsCardinalAccessible κ ∧
      (lowerMatchingEvaluation (C := C) r j).IsCardinalAccessible κ := by
  have := Smith.locallyPresentable_hasColimits (C := C)
  have : ∀ j, (lowerMatchingEvaluation (C := C) r j).IsAccessible.{w} :=
    fun j ↦ lowerMatchingEvaluation_isAccessible r j
  obtain ⟨κ, hκ, h⟩ := Smith.exists_common_accessibility
    (fun j ↦ lowerMatchingEvaluation (C := C) r j)
  exact ⟨κ, hκ, fun j ↦ ⟨lowerLatchingEvaluation_isCardinalAccessible r j κ, h j⟩⟩

end SerrePositivity.Reedy
