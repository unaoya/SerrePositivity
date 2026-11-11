module

public import SerrePositivity.HomotopicalAlgebra.Localization.AccessibleSmallLocalObjects
public import SerrePositivity.HomotopicalAlgebra.Localization.ChoiceIndependence

/-! # Accessibility of the original S-local objects and their inclusion

For an arbitrary small class S, the small-Hom detector constructs the
accessible local category. Actual universe comparison and resolution
choice independence identify it with the original locality predicate.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Bousfield
variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  [ModelCategory SSet.{w}] [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

lemma exists_accessible_localObjects
    (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
    (hcofW : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
    (hfibW : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
    (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
    (hcofB : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
    (hfibB : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)
    (S : MorphismProperty C) [S.IsSmall.{w}] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      IsCardinalAccessibleCategory (ObjectProperty.FullSubcategory
        (localObjects.{v, u} (C := C) cof fib S)) κ ∧
      (ObjectProperty.ι (localObjects.{v, u} (C := C) cof fib S)).IsCardinalAccessible κ := by
  obtain ⟨κ, hκ, d, hP, hi⟩ :=
    exists_accessible_smallLocalObjects_of_small.{w, v, u} I J hcofW hfibW S
  have he : smallLocalObjects.{w, v, u} d.cofibrationData d.fibrationData S =
      localObjects.{v, u} (C := C) cof fib S :=
    (smallLocalObjects_eq.{w, v, u} d.cofibrationData d.fibrationData
      hcofW hfibW hcofV hfibV hcofB hfibB S).trans
      (localObjects_choices_eq.{v, u} d.cofibrationData cof d.fibrationData fib hcofV S)
  rw [he] at hP hi
  exact ⟨κ, hκ, hP, hi⟩

end SerrePositivity.Bousfield
