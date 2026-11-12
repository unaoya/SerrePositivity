module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyColimit
public import SerrePositivity.HomotopicalAlgebra.Diagram.ColimitWeakEquivalence

/-! # Sufficiently filtered colimits compute actual homotopy colimits

The bound comes from the proved accessibility of the original weak
equivalences and their inclusion. It is independent of the small indexing
category, and works at every larger regular cardinal.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.DiagramModel.HomotopyColimit
variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

local instance : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)

lemma comparison_weakEquivalence_of_filtered (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [HasCardinalFilteredColimits.{w} (Smith.arrowProperty (weakEquivalences C)).FullSubcategory κ]
    [(Smith.arrowInclusion (weakEquivalences C)).IsCardinalAccessible κ]
    (K : Type w) [SmallCategory K] [IsCardinalFiltered K κ] (F : K ⥤ C) :
    weakEquivalences C ((comparison K I J).app F) :=
  filtered_colimitMap_weakEquivalence κ ((replacementComparison K I J).app F)
    (replacementComparison_objectwiseWeakEquivalence K I J F)

/-- The common bound is constructed from the original combinatorial model.
Every sufficiently filtered actual diagram is included. -/
lemma exists_filtered_comparison :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      ∀ (μ : Cardinal.{w}) [Fact μ.IsRegular], κ ≤ μ →
        ∀ (K : Type w) [SmallCategory K] [IsCardinalFiltered K μ] (F : K ⥤ C),
          weakEquivalences C ((comparison K I J).app F) := by
  obtain ⟨κ, hκ, hW, hι⟩ := Smith.exists_accessible_weakEquivalences I J
  refine ⟨κ, hκ, fun μ _ h K _ _ F ↦ ?_⟩
  have := IsCardinalFiltered.of_le K h
  exact comparison_weakEquivalence_of_filtered I J κ K F

end SerrePositivity.DiagramModel.HomotopyColimit
