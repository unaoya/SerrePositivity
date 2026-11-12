module

public import SerrePositivity.HomotopicalAlgebra.Localization.LocalReplacementDetection
public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleWeakEquivalenceInverseImage

/-! # Accessibility of W_S from an actual accessible local replacement

This proves the inverse-image/accessibility step for the original W_S.
The actual natural unit must be a local equivalence. That hypothesis is
explicit and has not yet been discharged for LocalFibrantApproximation;
therefore this file alone does not complete L2 or construct a localization.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Bousfield
variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{v}]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include I J hcof hfib in
lemma exists_accessible_localEquivalences_of_localUnit (S : MorphismProperty C)
    (R : C ⥤ C) [R.IsAccessible.{w}] (η : 𝟭 C ⟶ R)
    (hR : ∀ X, localObjects cof fib S (R.obj X))
    (hη : ∀ X, localEquivalences cof fib S (η.app X)) :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      IsCardinalAccessibleCategory
        (Smith.arrowProperty (localEquivalences cof fib S)).FullSubcategory κ ∧
      (Smith.arrowInclusion (localEquivalences cof fib S)).IsCardinalAccessible κ := by
  have := Smith.arrow_locallyPresentable (C := C)
  have := Smith.locallyPresentable_hasColimits (C := C)
  obtain ⟨κR, hκR, hRκ⟩ := Functor.IsAccessible.exists_cardinal R
  have := Smith.AccessibleFactorization.arrow_left_isCardinalAccessible (C := C) κR
  have := Smith.AccessibleFactorization.arrow_right_isCardinalAccessible (C := C) κR
  have : (R.mapArrow ⋙ Arrow.leftFunc).IsCardinalAccessible κR :=
    inferInstanceAs ((Arrow.leftFunc ⋙ R).IsCardinalAccessible κR)
  have : (R.mapArrow ⋙ Arrow.rightFunc).IsCardinalAccessible κR :=
    inferInstanceAs ((Arrow.rightFunc ⋙ R).IsCardinalAccessible κR)
  have : R.mapArrow.IsCardinalAccessible κR :=
    Smith.AccessibleFactorization.arrowFunctor_isCardinalAccessible _ κR
  have : R.mapArrow.IsAccessible.{w} := Functor.isAccessible_of_isCardinalAccessible _ κR
  have he : Smith.arrowProperty (localEquivalences cof fib S) =
      (Smith.arrowProperty (weakEquivalences C)).inverseImage R.mapArrow := by
    rw [localEquivalences_eq_inverseImage_of_localUnit cof fib hcof hfib S R η hR hη]
    rfl
  have h := Smith.exists_accessible_weakEquivalence_inverseImage I J R.mapArrow
  rw [← he] at h
  exact h

end SerrePositivity.Bousfield
