import SerrePositivity.HomotopicalAlgebra.Localization.ModelExistence
import Lean.Util.CollectAxioms

noncomputable section
universe w v u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Bousfield

variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
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


-- No localization certificate or generating trivial-cofibration class is supplied.
example (S : MorphismProperty C) [S.IsSmall.{w}] :
    Nonempty (ModelPresentation.{w} cof fib I S) :=
  exists_modelPresentation cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB S

-- The certificate includes the exact fibrant-object characterization in the original model.
example (S : MorphismProperty C) [S.IsSmall.{w}] :
    IsLocalizationModel.{v, u} cof fib S
      (modelPresentation cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB S).model := by
  exact ModelPresentation.isLocalizationModel cof fib I J IS JS hcof hfib hw
    hcofV hfibV hcofB hfibB _

example {S : MorphismProperty C} (p : ModelPresentation.{w} cof fib I S) :
    p.model.categoryWithWeakEquivalences.weakEquivalences.IsStableUnderCobaseChangeAgainst
      p.model.categoryWithCofibrations.cofibrations :=
  p.leftProper cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB

example {S : MorphismProperty C} (p : ModelPresentation.{w} cof fib I S) :
    let := p.model
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      Nonempty (SerrePositivity.Smith.AccessibleModelFactorizations C κ) :=
  p.exists_accessible_factorizations cof fib I

-- Left properness for W_S requires no smallness of S and no cofibrancy of the objects.
example (S : MorphismProperty C) :
    (localEquivalences.{v, u} (C := C) cof fib S).IsStableUnderCobaseChangeAgainst
      (cofibrations C) :=
  localEquivalences_leftProper cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB S

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Localization.ModelExistence,
    `SerrePositivity.HomotopicalAlgebra.Localization.LocalLeftProper]
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
  logInfo m!"Actual localization model audit passed: {count} declarations in {seen.size} modules."
