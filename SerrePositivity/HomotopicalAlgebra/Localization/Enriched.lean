module

public import SerrePositivity.HomotopicalAlgebra.Localization.Bifunctor
public import SerrePositivity.HomotopicalAlgebra.Enriched.TensorCotensor

/-! # Enriched model compatibility after ordinary localization

The ordinary localization is already constructed. Tensor compatibility
on the endpoints of the parameter's generating cofibrations is an
additional condition. It implies the full localized tensor axiom and the
actual enriched pullback-hom SM7 condition. No simplicial enrichment or
cofibrancy of generating domains in C is required.
-/

@[expose] public section
universe wV wC vV uV vC uC
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.Bousfield.IsLocalizationModel
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [base : ModelCategory V]
  {C : Type uC} [Category.{vC} C] [original : ModelCategory C]
  [EnrichedOrdinaryCategory V C] [simplicial : ModelCategory SSet.{vC}]
  {cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)}
  {fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C)}
  {S : MorphismProperty C} {m : ModelCategory C}
  (h : @IsLocalizationModel C _ original simplicial cof fib S m)
  (hcof : simplicial.categoryWithCofibrations.cofibrations = MorphismProperty.monomorphisms _)
  (hfib : simplicial.categoryWithFibrations.fibrations = SSet.modelCategoryQuillen.J.{vC}.rlp)
  (P : SerrePositivity.Enriched.TensorCotensor V C)
  (hP : @Quillen.IsQuillenBifunctor V _ base C _ original C _ original P.tensor)
  (IV JV : MorphismProperty V) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{wV} IV JV]
  (IC JC : MorphismProperty C) [@_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{wC} C _ m IC JC]

include h hcof hfib P hP IV JV IC JC in
lemma enriched_model_of_tensor_compatible
    (hdom : ∀ {A B : V} (i : A ⟶ B), IV i → IsCofibrant A)
    (hcompat : ∀ {A B : V} (i : A ⟶ B), IV i → ∀ {X Y : C} (s : X ⟶ Y), S s →
      (@localEquivalences C _ original simplicial cof fib S)
        ((P.tensor.obj A).map ((@cofibrantSource C _ original cof).map s)) ∧
      (@localEquivalences C _ original simplicial cof fib S)
        ((P.tensor.obj B).map ((@cofibrantSource C _ original cof).map s))) :
    @Quillen.IsQuillenBifunctor V _ base C _ m C _ m P.tensor ∧
      @Quillen.HasQuillenPullbackHom C _ m V _ base C _ m (eHomFunctor V C) ∧
      @Quillen.HasQuillenPullbackHom V _ base C _ m C _ m P.cotensor := by
  let := original
  have hQ := h.bifunctor_of_tensor_compatible hcof hfib P.tensorCotensor P.tensorHom
    hP IV JV IC JC hdom hcompat
  let := m
  exact ⟨hQ, (SerrePositivity.Enriched.tensor_iff_mapping_model P).mp hQ,
    (SerrePositivity.Enriched.tensor_iff_cotensor_model P).mp hQ⟩

end SerrePositivity.Bousfield.IsLocalizationModel
