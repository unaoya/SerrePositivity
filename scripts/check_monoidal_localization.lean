import SerrePositivity.HomotopicalAlgebra.Localization.MonoidalExistence
import SerrePositivity.HomotopicalAlgebra.Localization.ModelExistence
import Lean.Util.CollectAxioms

noncomputable section
universe w v u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.MonoidalCategory
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



variable [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]

-- No cofibrant-unit assumption, and no assumed localized pushout-product or unit axiom.
example {S : MorphismProperty C} (p : ModelPresentation.{w} cof fib I S)
    (hF : @SerrePositivity.Quillen.IsQuillenBifunctor C _ original C _ original C _ original
      (curriedTensor C))
    (hu : @SerrePositivity.Quillen.HasUnitAxiom C _ original _)
    (hdom : ∀ {A B : C} (i : A ⟶ B), I i → IsCofibrant A)
    (hcompat : ∀ {A B : C} (i : A ⟶ B), I i → ∀ {X Y : C} (s : X ⟶ Y), S s →
      localEquivalences.{v, u} (C := C) cof fib S
        (((curriedTensor C).obj A).map ((cofibrantSource cof).map s)) ∧
      localEquivalences.{v, u} (C := C) cof fib S
        (((curriedTensor C).obj B).map ((cofibrantSource cof).map s))) :
    @SerrePositivity.Quillen.MonoidalModelCategory C _ p.model _ ∧
      @SerrePositivity.Quillen.HasQuillenPullbackHom C _ p.model C _ p.model C _ p.model
        (MonoidalClosed.internalHom (C := C)) := by
  let G := p.generators
  have := p.generated
  have h := p.isLocalizationModel cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB
  have hm := h.monoidal_model_of_tensor_compatible hcofV hfibV I J G hF hu hdom hcompat
  have hp : @SerrePositivity.Quillen.HasQuillenPullbackHom C _ p.model C _ p.model C _ p.model
      (MonoidalClosed.internalHom (C := C)) := by
    let := p.model
    exact ((SerrePositivity.Quillen.monoidalModelCategory_iff C).mp hm).1
  exact ⟨hm, hp⟩

-- Final original inputs produce the actual monoidal localized model.
example (S : MorphismProperty C) [S.IsSmall.{w}]
    (hM : @SerrePositivity.Quillen.MonoidalModelCategory C _ original _)
    (hdom : ∀ {A B : C} (i : A ⟶ B), I i → IsCofibrant A)
    (hcompat : ∀ {A B : C} (i : A ⟶ B), I i → ∀ {X Y : C} (s : X ⟶ Y), S s →
      localEquivalences.{v, u} (C := C) cof fib S
        (((curriedTensor C).obj A).map ((cofibrantSource cof).map s)) ∧
      localEquivalences.{v, u} (C := C) cof fib S
        (((curriedTensor C).obj B).map ((cofibrantSource cof).map s))) :
    ∃ p : ModelPresentation.{w} cof fib I S,
      @SerrePositivity.Quillen.MonoidalModelCategory C _ p.model _ := by
  have := hM
  exact exists_monoidal_localization cof fib I J IS JS hcof hfib hw
    hcofV hfibV hcofB hfibB S hdom hcompat

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Monoidal.BifunctorSymmetrize,
    `SerrePositivity.HomotopicalAlgebra.Localization.Monoidal,
    `SerrePositivity.HomotopicalAlgebra.Localization.MonoidalExistence]
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
  logInfo m!"Monoidal localization audit passed: {count} declarations in {seen.size} modules."
