import SerrePositivity.HomotopicalAlgebra.Localization.EnrichedExistence
import Lean.Util.CollectAxioms

noncomputable section
universe w v u wV vV uV
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.MonoidalCategory
open SerrePositivity SerrePositivity.Bousfield
open SerrePositivity.InfinityCategories.HA.ModelCategoryComparison (CofibrantlyGenerated)

section General
variable {C : Type u} [Category.{v} C] [original : ModelCategory C] [IsLocallyPresentable.{w} C]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (I J : MorphismProperty C) [CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w}) [CofibrantlyGenerated.{w} IS JS]
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
  (IV JV : MorphismProperty V) [CofibrantlyGenerated.{wV} IV JV]
  [ModelCategory SSet.{vV}] [ModelCategory SSet.{max v vV}]
  (hcofParam : cofibrations SSet.{vV} = MorphismProperty.monomorphisms _)
  (hfibParam : fibrations SSet.{vV} = SSet.modelCategoryQuillen.J.{vV}.rlp)
  (hcofJoin : cofibrations SSet.{max v vV} = MorphismProperty.monomorphisms _)
  (hfibJoin : fibrations SSet.{max v vV} = SSet.modelCategoryQuillen.J.{max v vV}.rlp)


-- Construct the model and all compatibility data; none is assumed for a localized model.
example (S : MorphismProperty C) [S.IsSmall.{w}]
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
        SerrePositivity.Enriched.localObjects (V := V) cof fib S Y :=
  exists_enriched_localization cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB
    P IV JV hcofParam hfibParam hcofJoin hfibJoin S hdom hcompat
end General

section Simplicial
variable {C : Type u} [Category.{v} C] [original : ModelCategory C] [IsLocallyPresentable.{w} C]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (I J : MorphismProperty C) [CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w}) [CofibrantlyGenerated.{w} IS JS]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hw : weakEquivalences SSet.{w} = SerrePositivity.SimplicialHomotopy.weakEquivalences)
  [simplicial : ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcofB : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfibB : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)
  [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]



variable [EnrichedOrdinaryCategory SSet.{v} C]
  (P : SerrePositivity.Enriched.TensorCotensor SSet.{v} C) [Quillen.IsQuillenBifunctor P.tensor]
  (IV JV : MorphismProperty SSet.{v}) [CofibrantlyGenerated.{v} IV JV]

-- For V = SSet, the parameter cofibrancy and action unit conditions are proved automatically.
example (S : MorphismProperty C) [S.IsSmall.{w}]
    (hcompat : ∀ {A B : SSet.{v}} (i : A ⟶ B), IV i → ∀ {X Y : C} (s : X ⟶ Y), S s →
      localEquivalences.{v, u} (C := C) cof fib S
        ((P.tensor.obj A).map ((HomotopyFunctionComplex.cofibrantSource cof).map s)) ∧
      localEquivalences.{v, u} (C := C) cof fib S
        ((P.tensor.obj B).map ((HomotopyFunctionComplex.cofibrantSource cof).map s))) :
    ∃ p : ModelPresentation.{w} cof fib I S,
      @Quillen.IsQuillenBifunctor SSet.{v} _ simplicial C _ p.model C _ p.model P.tensor ∧
      p.model.categoryWithWeakEquivalences.weakEquivalences =
        SerrePositivity.Enriched.localEquivalences (V := SSet.{v}) cof fib S := by
  have : IsCofibrant (𝟙_ SSet.{v}) := by
    constructor
    rw [hcofV]
    exact inferInstanceAs (Mono _)
  have : SerrePositivity.Enriched.HasTensorUnitAxiom P :=
    SerrePositivity.Enriched.tensorUnitAxiom_of_cofibrant_unit P
  have hdom {A B : SSet.{v}} (i : A ⟶ B) (_hi : IV i) : IsCofibrant A := by
    constructor
    rw [hcofV]
    exact inferInstanceAs (Mono _)
  obtain ⟨p, hq, _, _, _, _, he, _⟩ :=
    exists_enriched_localization (V := SSet.{v}) (base := simplicial)
      cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB P IV JV
      hcofV hfibV hcofV hfibV S hdom hcompat
  exact ⟨p, hq, he⟩
end Simplicial

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Enriched.UnitChangeModel,
    `SerrePositivity.HomotopicalAlgebra.Localization.EnrichedExistence]
  let mut count : Nat := 0
  let mut seen : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  for mod in expected do
    unless seen.contains mod do throwError "Module not audited: {mod}"
  logInfo m!"Actual enriched localization audit passed: {count} declarations in {seen.size} modules."
