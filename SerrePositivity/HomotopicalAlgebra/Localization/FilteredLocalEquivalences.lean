module

public import SerrePositivity.HomotopicalAlgebra.Localization.HocolimLocalEquivalences
public import SerrePositivity.HomotopicalAlgebra.Diagram.FilteredHomotopyColimit

/-! # Uniform sufficiently filtered colimits preserve the original W_S

The bound comes from the original model's weak equivalences, before
accessibility of W_S is known. It is independent of S and of the diagrams.
This is not a statement about arbitrary transfinite composites.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DiagramModel

namespace SerrePositivity.Bousfield
variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hw : weakEquivalences SSet.{w} = SimplicialHomotopy.weakEquivalences)
  [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcofB : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfibB : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)

local instance : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)

include I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
lemma exists_filtered_localEquivalence_colim :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      ∀ (μ : Cardinal.{w}) [Fact μ.IsRegular], κ ≤ μ →
        ∀ (K : Type w) [SmallCategory K] [IsCardinalFiltered K μ]
          (S : MorphismProperty C) {D E : K ⥤ C} (a : D ⟶ E),
          (∀ k, localEquivalences.{v, u} cof fib S (a.app k)) →
          localEquivalences.{v, u} cof fib S ((colim : (K ⥤ C) ⥤ C).map a) := by
  obtain ⟨κ, hκ, hcomp⟩ := HomotopyColimit.exists_filtered_comparison I J
  refine ⟨κ, hκ, fun μ _ hμ K _ _ S D E a ha => ?_⟩
  exact HocolimSourceTests.localEquivalence_colim_of_weakComparisons K I J IS JS cof fib
    hcof hfib hw hcofV hfibV hcofB hfibB S a ha
    (hcomp μ hμ K D) (hcomp μ hμ K E)

end SerrePositivity.Bousfield
