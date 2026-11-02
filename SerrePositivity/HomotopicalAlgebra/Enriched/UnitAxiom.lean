module

public import SerrePositivity.CategoryTheory.Enriched.TensorCotensor
public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-! # The unit axiom for an enriched tensor action

This is separate from the pushout-product axiom. A specified cofibrant
replacement of the enriching unit must act by weak equivalences on
cofibrant objects of C. A cofibrant enriching unit supplies the identity
replacement; a noncofibrant unit is allowed with the explicit unit axiom.
-/

@[expose] public section
universe vV uV vC uC
noncomputable section
open CategoryTheory HomotopicalAlgebra
open CategoryTheory.MonoidalCategory

namespace SerrePositivity.Enriched
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [ModelCategory V]
  {C : Type uC} [Category.{vC} C] [ModelCategory C] [EnrichedOrdinaryCategory V C]
  (P : TensorCotensor V C)

structure TensorUnitReplacementAxiom (U : V) (q : U ⟶ 𝟙_ V) : Prop where
  cofibrant : IsCofibrant U
  weakEquivalence : WeakEquivalence q
  tensor (X : C) : IsCofibrant X →
    weakEquivalences C ((P.tensor.map q).app X ≫ P.unitMap X)

class HasTensorUnitAxiom : Prop where
  exists_replacement : ∃ (U : V) (q : U ⟶ 𝟙_ V), TensorUnitReplacementAxiom P U q

lemma tensorUnitAxiom_of_cofibrant_unit [IsCofibrant (𝟙_ V)] : HasTensorUnitAxiom P := by
  refine ⟨𝟙_ V, 𝟙 _, ⟨inferInstance, inferInstance, ?_⟩⟩
  intro X _
  have he : (P.tensor.map (𝟙 (𝟙_ V))).app X = 𝟙 _ := congr_app (P.tensor.map_id _) X
  rw [he, Category.id_comp]
  exact (weakEquivalences C).of_isIso (P.unitMap X)

end SerrePositivity.Enriched
