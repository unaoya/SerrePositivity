module

public import SerrePositivity.HomotopicalAlgebra.Localization.ModelExistence
public import SerrePositivity.HomotopicalAlgebra.Localization.EnrichedDetection
public import SerrePositivity.HomotopicalAlgebra.Enriched.UnitChangeModel

/-! # Actual enriched localization with derived-Hom detection

Construct the ordinary localization, derive its tensor model axiom from
the stated endpoint compatibility, and identify its objects and weak
equivalences with the actual V-valued derived Hom tests. The action unit
axiom is inherited, including when the enriching unit is noncofibrant.
-/

@[expose] public section
universe w v u wV vV uV
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Bousfield
variable {C : Type u} [Category.{v} C] [original : ModelCategory C] [IsLocallyPresentable.{w} C]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hw : weakEquivalences SSet.{w} = SimplicialHomotopy.weakEquivalences)
  [simplicialV : ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcofB : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfibB : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)
  [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [base : ModelCategory V]
  [EnrichedOrdinaryCategory V C]
  (P : SerrePositivity.Enriched.TensorCotensor V C)
  [hP : Quillen.IsQuillenBifunctor P.tensor] [hunit : SerrePositivity.Enriched.HasTensorUnitAxiom P]
  (IV JV : MorphismProperty V) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{wV} IV JV]
  [ModelCategory SSet.{vV}] [ModelCategory SSet.{max v vV}]
  (hcofParam : cofibrations SSet.{vV} = MorphismProperty.monomorphisms _)
  (hfibParam : fibrations SSet.{vV} = SSet.modelCategoryQuillen.J.{vV}.rlp)
  (hcofJoin : cofibrations SSet.{max v vV} = MorphismProperty.monomorphisms _)
  (hfibJoin : fibrations SSet.{max v vV} = SSet.modelCategoryQuillen.J.{max v vV}.rlp)

include I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB IV JV
  hcofParam hfibParam hcofJoin hfibJoin in
lemma exists_enriched_localization (S : MorphismProperty C) [S.IsSmall.{w}]
    (hdom : ∀ {A B : V} (i : A ⟶ B), IV i → IsCofibrant A)
    (hcompat : ∀ {A B : V} (i : A ⟶ B), IV i → ∀ {X Y : C} (s : X ⟶ Y), S s →
      localEquivalences.{v, u} (C := C) cof fib S
        ((P.tensor.obj A).map ((HomotopyFunctionComplex.cofibrantSource cof).map s)) ∧
      localEquivalences.{v, u} (C := C) cof fib S
        ((P.tensor.obj B).map ((HomotopyFunctionComplex.cofibrantSource cof).map s))) :
    ∃ p : ModelPresentation.{w} cof fib I S,
      @Quillen.IsQuillenBifunctor V _ base C _ p.model C _ p.model P.tensor ∧
      @Quillen.HasQuillenPullbackHom C _ p.model V _ base C _ p.model (eHomFunctor V C) ∧
      @Quillen.HasQuillenPullbackHom V _ base C _ p.model C _ p.model P.cotensor ∧
      @SerrePositivity.Enriched.HasTensorUnitAxiom V _ _ base C _ p.model _ P ∧
      (localObjects.{v, u} (C := C) cof fib S =
        SerrePositivity.Enriched.localObjects (V := V) cof fib S) ∧
      (p.model.categoryWithWeakEquivalences.weakEquivalences =
        SerrePositivity.Enriched.localEquivalences (V := V) cof fib S) ∧
      ∀ Y, p.model.categoryWithFibrations.fibrations (terminal.from Y) ↔ IsFibrant Y ∧
        SerrePositivity.Enriched.localObjects (V := V) cof fib S Y := by
  let p := modelPresentation cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB S
  let G := p.generators
  have := p.generated
  have hc := p.isLocalizationModel cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB
  have hn := hc.enriched_model_of_tensor_compatible hcofV hfibV P hP IV JV I G hdom hcompat
  have := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_cofibration_trivialFibration IV JV
  let cofParam := MorphismProperty.functorialFactorizationData
    (cofibrations V) (trivialFibrations V)
  have ho := hc.localObjects_eq_enriched (V := V) hcofV hfibV P hP hn.1 hunit cofParam
    hcofParam hfibParam hcofJoin hfibJoin
  have he := hc.localEquivalences_eq_enriched (V := V) hcofV hfibV P hP hn.1 hunit cofParam
    hcofParam hfibParam hcofJoin hfibJoin
  have hy := hc.fibrant_iff_enriched (V := V) hcofV hfibV P hP hn.1 hunit cofParam
    hcofParam hfibParam hcofJoin hfibJoin
  have hu := SerrePositivity.Enriched.hasTensorUnitAxiom_change_model original p.model P
    hc.cofibrations_eq
    ((weakEquivalences_le_localEquivalences cof fib hcofV S).trans
      hc.weakEquivalences_eq.symm.le) hunit
  exact ⟨p, hn.1, hn.2.1, hn.2.2, hu, ho, p.weakEquivalences_eq.trans he, hy⟩

end SerrePositivity.Bousfield
