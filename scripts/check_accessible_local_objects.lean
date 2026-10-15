import SerrePositivity.HomotopicalAlgebra.Localization.AccessibleLocalObjects
import Lean.Util.CollectAxioms

noncomputable section
universe w v u
open CategoryTheory HomotopicalAlgebra
open SerrePositivity SerrePositivity.Bousfield

variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  [ModelCategory SSet.{w}]
  (I J : MorphismProperty C) [ModelGeneration.CofibrantlyGenerated.{w} I J]
  (hcofW : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfibW : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)

-- Final combinatorial inputs and an arbitrary small class S suffice.
-- The subcategory itself and its actual inclusion are both covered.
example (S : MorphismProperty C) [S.IsSmall.{w}] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      ∃ d : Smith.AccessibleModelFactorizations C κ,
        IsCardinalAccessibleCategory (ObjectProperty.FullSubcategory
          (smallLocalObjects.{w, v, u} d.cofibrationData d.fibrationData S)) κ ∧
        Functor.IsCardinalAccessible (ObjectProperty.ι
          (smallLocalObjects.{w, v, u} d.cofibrationData d.fibrationData S)) κ :=
  exists_accessible_smallLocalObjects_of_small.{w, v, u} I J hcofW hfibW S

variable [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcofB : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfibB : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)

-- Recover the original locality predicate, for any original choices,
-- without assuming that its mapping-test functors are accessible.
example (S : MorphismProperty C) [S.IsSmall.{w}] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      IsCardinalAccessibleCategory (ObjectProperty.FullSubcategory
        (localObjects.{v, u} cof fib S)) κ ∧
      (ObjectProperty.ι (localObjects.{v, u} cof fib S)).IsCardinalAccessible κ :=
  exists_accessible_localObjects cof fib I J hcofW hfibW hcofV hfibV hcofB hfibB S

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Localization.MappingTestDiagram,
    `SerrePositivity.HomotopicalAlgebra.Localization.AccessibleSmallLocalObjects,
    `SerrePositivity.HomotopicalAlgebra.Localization.AccessibleLocalObjects]
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
  logInfo m!"Accessible local objects audit passed: {count} declarations in {seen.size} modules."
