import SerrePositivity.HomotopicalAlgebra.Localization.IteratedExistence
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



-- The only extra inputs are two small classes of arbitrary original maps.
-- The first model, its factorizations, and its actual T-localization are constructed.
example (S T : MorphismProperty C) [S.IsSmall.{w}] [T.IsSmall.{w}] :
    ∃ (pS : ModelPresentation.{w} cof fib I S)
      (pST : ModelPresentation.{w} cof fib I (S ⊔ T)),
      ∃ (cofS : MorphismProperty.FunctorialFactorizationData
          pS.model.categoryWithCofibrations.cofibrations
          (pS.model.categoryWithFibrations.fibrations ⊓
            pS.model.categoryWithWeakEquivalences.weakEquivalences))
        (fibS : MorphismProperty.FunctorialFactorizationData
          (pS.model.categoryWithCofibrations.cofibrations ⊓
            pS.model.categoryWithWeakEquivalences.weakEquivalences)
          pS.model.categoryWithFibrations.fibrations),
        @IsLocalizationModel C _ pS.model _ cofS fibS T pST.model :=
  exists_iterated_localization cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB S T

-- The union presentation can be any actual one, independently of its generating family.
example {S T : MorphismProperty C} [T.IsSmall.{w}]
    (pS : ModelPresentation.{w} cof fib I S) (pST : ModelPresentation.{w} cof fib I (S ⊔ T)) :
    ∃ (cofS : MorphismProperty.FunctorialFactorizationData
        pS.model.categoryWithCofibrations.cofibrations
        (pS.model.categoryWithFibrations.fibrations ⊓
          pS.model.categoryWithWeakEquivalences.weakEquivalences))
      (fibS : MorphismProperty.FunctorialFactorizationData
        (pS.model.categoryWithCofibrations.cofibrations ⊓
          pS.model.categoryWithWeakEquivalences.weakEquivalences)
        pS.model.categoryWithFibrations.fibrations),
      @IsLocalizationModel C _ pS.model _ cofS fibS T pST.model :=
  pS.exists_iterated_certificate cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB pST

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Quillen.ModelOrder,
    `SerrePositivity.HomotopicalAlgebra.Localization.Minimality,
    `SerrePositivity.HomotopicalAlgebra.Localization.Iteration,
    `SerrePositivity.HomotopicalAlgebra.Localization.IteratedExistence]
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
  logInfo m!"Iterated localization model audit passed: {count} declarations in {seen.size} modules."
