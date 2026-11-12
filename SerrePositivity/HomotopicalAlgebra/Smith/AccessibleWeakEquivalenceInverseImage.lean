module

public import SerrePositivity.HomotopicalAlgebra.Smith.WeakEquivalencesAccessible

/-! # Accessible inverse images of original model weak equivalences

The source only needs local presentability and the test functor must be
accessible. The target is a combinatorial model category. The proof uses
its actual accessible factorization and the proved small-right-class
inverse-image theorem, not a claim about arbitrary accessible full images.
-/

@[expose] public section
universe w v₁ v₂ u₁ u₂
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Smith

lemma exists_accessible_weakEquivalence_inverseImage
    {C : Type u₁} [Category.{v₁} C] [IsLocallyPresentable.{w} C]
    {E : Type u₂} [Category.{v₂} E] [ModelCategory E] [IsLocallyPresentable.{w} E]
    (I J : MorphismProperty E) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
    (F : C ⥤ Arrow E) [F.IsAccessible.{w}] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      IsCardinalAccessibleCategory
        ((arrowProperty (weakEquivalences E)).inverseImage F).FullSubcategory κ ∧
      (((arrowProperty (weakEquivalences E)).inverseImage F).ι).IsCardinalAccessible κ := by
  have := locallyPresentable_hasColimits (C := E)
  have : I.IsSmall.{w} := by
    obtain ⟨μ, hμ, hb, hI⟩ := MorphismProperty.HasSmallObjectArgument.exists_cardinal (I := I)
    exact SmallObject.isSmall I μ
  obtain ⟨κ₀, h₀, ⟨d⟩⟩ := exists_accessible_model_factorizations E I J
  let R := AccessibleFactorization.rightFactor d.fibrationData
  have : R.IsCardinalAccessible κ₀ := by
    have := d.fibrationAccessible
    exact AccessibleFactorization.rightFactor_isCardinalAccessible d.fibrationData κ₀
  have : R.IsAccessible.{w} := R.isAccessible_of_isCardinalAccessible κ₀
  have : (F ⋙ R).IsAccessible.{w} := inferInstance
  have h := exists_accessible_rightClass_inverseImage I (F ⋙ R)
  have hI := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.rlp_I (I := I) (J := J)
  have he : (arrowProperty (weakEquivalences E)).inverseImage F =
      (arrowProperty I.rlp).inverseImage (F ⋙ R) := by
    rw [WeakEquivalenceFilteredColimits.arrowProperty_eq_inverseImage d.fibrationData I hI]
    rfl
  rw [he]
  exact h

end SerrePositivity.Smith
