module

public import SerrePositivity.HomotopicalAlgebra.Localization.UniversalProperty
public import SerrePositivity.HomotopicalAlgebra.Quillen.ModelOrder

/-! # Minimality among model structures with the same cofibrations

An actual localization has the smallest model weak-equivalence class
containing the original weak equivalences and S, with cofibrations fixed.
This is a consequence of the proved Quillen universal property, not an
extra description assumed of the local-equivalence class.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.Bousfield.IsLocalizationModel
variable {C : Type u} [Category.{v} C] [original : ModelCategory C]
  [simplicial : ModelCategory SSet.{v}]
  {cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)}
  {fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C)}
  {S : MorphismProperty C} {m : ModelCategory C}
  (h : @IsLocalizationModel C _ original simplicial cof fib S m)
  (hcof : simplicial.categoryWithCofibrations.cofibrations = MorphismProperty.monomorphisms _)
  (hfib : simplicial.categoryWithFibrations.fibrations = SSet.modelCategoryQuillen.J.{v}.rlp)

include h hcof hfib in
lemma identity_leftQuillen_of_contains (n : ModelCategory C)
    (hc : n.categoryWithCofibrations.cofibrations = original.categoryWithCofibrations.cofibrations)
    (hW : original.categoryWithWeakEquivalences.weakEquivalences ≤
      n.categoryWithWeakEquivalences.weakEquivalences)
    (hS : S ≤ n.categoryWithWeakEquivalences.weakEquivalences) :
    @Quillen.IsLeftQuillen C _ C _ m.categoryWithCofibrations m.categoryWithWeakEquivalences
      n.categoryWithCofibrations n.categoryWithWeakEquivalences (𝟭 C) := by
  let := original
  have hn : @Quillen.IsLeftQuillen C _ C _ original.categoryWithCofibrations
      original.categoryWithWeakEquivalences n.categoryWithCofibrations
      n.categoryWithWeakEquivalences (𝟭 C) := by
    refine @Quillen.IsLeftQuillen.mk C _ C _ original.categoryWithCofibrations
      original.categoryWithWeakEquivalences n.categoryWithCofibrations
      n.categoryWithWeakEquivalences (𝟭 C) ?_ ?_
    · exact fun _ _ f hf => hc.symm.le f hf
    · exact fun _ _ f hf => ⟨hc.symm.le f hf.1, hW f hf.2⟩
  apply (h.leftQuillen_iff_cofibrant_test (target := n) hcof hfib (Adjunction.id) hn
    hcof hfib hcof hfib).mpr
  intro X Z f hf
  let Q := cofibrantSource cof
  let q := cofibrantSourceComparison cof
  have hqX := hW _ (cofibrantSourceComparison_trivialFibration cof X).2
  have hqZ := hW _ (cofibrantSourceComparison_trivialFibration cof Z).2
  have : n.categoryWithWeakEquivalences.weakEquivalences.HasTwoOutOfThreeProperty := n.cm2
  exact n.categoryWithWeakEquivalences.weakEquivalences.of_postcomp _ _ hqZ
    ((q.naturality f).symm ▸ n.categoryWithWeakEquivalences.weakEquivalences.comp_mem _ _
      hqX (hS f hf))

include h hcof hfib in
lemma weakEquivalences_le_of_contains (n : ModelCategory C)
    (hc : n.categoryWithCofibrations.cofibrations = original.categoryWithCofibrations.cofibrations)
    (hW : original.categoryWithWeakEquivalences.weakEquivalences ≤
      n.categoryWithWeakEquivalences.weakEquivalences)
    (hS : S ≤ n.categoryWithWeakEquivalences.weakEquivalences) :
    m.categoryWithWeakEquivalences.weakEquivalences ≤
      n.categoryWithWeakEquivalences.weakEquivalences := by
  let := original
  exact Quillen.weakEquivalences_le_of_identity_leftQuillen m n
    (h.cofibrations_eq.trans hc.symm) (h.identity_leftQuillen_of_contains hcof hfib n hc hW hS)

end SerrePositivity.Bousfield.IsLocalizationModel
