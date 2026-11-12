module

public import SerrePositivity.HomotopicalAlgebra.Localization.LocalBoundaryEquivalences
public import SerrePositivity.HomotopicalAlgebra.Localization.AccessibleLocalEquivalences

/-! # Actual accessible local replacement and accessibility of original W_S

The generated unit is proved to be a local equivalence, discharging the
hypothesis in the conditional inverse-image theorem. Neither that unit
condition nor accessibility of W_S is supplied as an input.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Bousfield
variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hw : weakEquivalences SSet.{w} = SimplicialHomotopy.weakEquivalences)
  [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcofB : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfibB : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)
  [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]


include I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
lemma exists_accessible_localReplacement (S : MorphismProperty C) [S.IsSmall.{w}] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular) (R : C ⥤ C) (η : 𝟭 C ⟶ R),
      R.IsCardinalAccessible κ ∧
      ∀ X, cofibrations C (η.app X) ∧
        localEquivalences.{v, u} (C := C) cof fib S (η.app X) ∧
        localFibrantObjects.{v, u} (C := C) cof fib S (R.obj X) := by
  obtain ⟨κ, hκ, d, _hd, hR, hη, hlocal⟩ :=
    LocalFibrantApproximation.exists_accessible_approximation I J cof S fib hcofV
  exact ⟨κ, hκ, Smith.AccessibleFactorization.terminalRestriction d,
    Smith.AccessibleFactorization.terminalComparison d, hR, fun X =>
      ⟨hη X, localFibrant_approximation_unit_localEquivalence cof fib I J IS JS hcof hfib hw
        hcofV hfibV hcofB hfibB S d X, hlocal X⟩⟩

include I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
/-- Accessibility of the actual original local-equivalence class and its arrow inclusion. -/
lemma exists_accessible_localEquivalences (S : MorphismProperty C) [S.IsSmall.{w}] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      IsCardinalAccessibleCategory
        (Smith.arrowProperty (localEquivalences.{v, u} (C := C) cof fib S)).FullSubcategory κ ∧
      Functor.IsCardinalAccessible
        (Smith.arrowInclusion (localEquivalences.{v, u} (C := C) cof fib S)) κ := by
  obtain ⟨κ, hκ, R, η, hR, hX⟩ := exists_accessible_localReplacement cof fib I J IS JS
    hcof hfib hw hcofV hfibV hcofB hfibB S
  have : R.IsCardinalAccessible κ := hR
  have : R.IsAccessible.{w} := Functor.isAccessible_of_isCardinalAccessible _ κ
  exact exists_accessible_localEquivalences_of_localUnit I J cof fib hcofV hfibV S R η
    (fun X => (hX X).2.2.2) (fun X => (hX X).2.1)

end SerrePositivity.Bousfield
