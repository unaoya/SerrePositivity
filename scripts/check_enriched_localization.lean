import SerrePositivity.HomotopicalAlgebra.Localization.Enriched
import SerrePositivity.HomotopicalAlgebra.Localization.MonoidalUnit
import SerrePositivity.HomotopicalAlgebra.Localization.ModelExistence
import Lean.Util.CollectAxioms

noncomputable section
universe w v u wV vV uV
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Bousfield SerrePositivity.HomotopyFunctionComplex

variable {C : Type u} [Category.{v} C] [original : ModelCategory C] [IsLocallyPresentable.{w} C]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w}) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hw : weakEquivalences SSet.{w} = SerrePositivity.SimplicialHomotopy.weakEquivalences)
  [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcofB : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfibB : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)
  [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]



variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [base : ModelCategory V]
  [EnrichedOrdinaryCategory V C]
  (P : SerrePositivity.Enriched.TensorCotensor V C)
  (hP : @SerrePositivity.Quillen.IsQuillenBifunctor V _ base C _ original C _ original P.tensor)
  (IV JV : MorphismProperty V) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{wV} IV JV]

-- Use the actual localized model's generated class, with no assumption on its domains.
example {S : MorphismProperty C} (p : ModelPresentation.{w} cof fib I S)
    (hdom : ∀ {A B : V} (i : A ⟶ B), IV i → IsCofibrant A)
    (hcompat : ∀ {A B : V} (i : A ⟶ B), IV i → ∀ {X Y : C} (s : X ⟶ Y), S s →
      localEquivalences.{v, u} (C := C) cof fib S
        ((P.tensor.obj A).map ((cofibrantSource cof).map s)) ∧
      localEquivalences.{v, u} (C := C) cof fib S
        ((P.tensor.obj B).map ((cofibrantSource cof).map s))) :
    @SerrePositivity.Quillen.IsQuillenBifunctor V _ base C _ p.model C _ p.model P.tensor ∧
      @SerrePositivity.Quillen.HasQuillenPullbackHom C _ p.model V _ base C _ p.model
        (eHomFunctor V C) ∧
      @SerrePositivity.Quillen.HasQuillenPullbackHom V _ base C _ p.model C _ p.model
        P.cotensor := by
  let G := p.generators
  have := p.generated
  have h := p.isLocalizationModel cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB
  exact h.enriched_model_of_tensor_compatible hcofV hfibV P hP IV JV I G hdom hcompat

-- The unit axiom is inherited separately, without assuming a cofibrant unit.
example [MonoidalCategory C] {S : MorphismProperty C} (p : ModelPresentation.{w} cof fib I S)
    (hu : @SerrePositivity.Quillen.HasUnitAxiom C _ original _) :
    @SerrePositivity.Quillen.HasUnitAxiom C _ p.model _ := by
  have h := p.isLocalizationModel cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB
  exact h.hasUnitAxiom hcofV hu

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Monoidal.EndpointBifunctor,
    `SerrePositivity.HomotopicalAlgebra.Monoidal.BifunctorChangeModel,
    `SerrePositivity.HomotopicalAlgebra.Monoidal.UnitChangeModel,
    `SerrePositivity.HomotopicalAlgebra.Localization.Endofunctor,
    `SerrePositivity.HomotopicalAlgebra.Localization.Bifunctor,
    `SerrePositivity.HomotopicalAlgebra.Localization.Enriched,
    `SerrePositivity.HomotopicalAlgebra.Localization.MonoidalUnit]
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
  logInfo m!"Enriched localization tensor compatibility audit passed: {count} declarations in {seen.size} modules."
