import SerrePositivity.HomotopicalAlgebra.Localization.QuillenCriterion
import Lean.Util.CollectAxioms

noncomputable section
universe vC uC vD uD
open CategoryTheory HomotopicalAlgebra
open SerrePositivity

-- Arbitrary ordinary model categories, with no specified functorial factorizations.
section General
variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]

example {A B : C} (j : A ⟶ B)
    (h : ∀ {X Y : C} (p : X ⟶ Y), IsFibrant X → IsFibrant Y →
      Fibration p → HasLiftingProperty j p) : weakEquivalences C j :=
  Quillen.weakEquivalence_of_lifts_fibrant_fibrations j h

example {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) :
    Quillen.IsLeftQuillen L ↔ (cofibrations C ≤ (cofibrations D).inverseImage L) ∧
      ∀ {X Y : D} (p : X ⟶ Y), IsFibrant X → IsFibrant Y →
        Fibration p → fibrations C (R.map p) :=
  Quillen.isLeftQuillen_iff_fibrant_test adj
end General

section Localization
variable {C : Type uC} [Category.{vC} C] [original : ModelCategory C]
  [simplicial : ModelCategory SSet.{vC}]
  {cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)}
  {fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C)}
  {S : MorphismProperty C} {m : ModelCategory C}
  (h : @Bousfield.IsLocalizationModel C _ original simplicial cof fib S m)
  (hcof : simplicial.categoryWithCofibrations.cofibrations = MorphismProperty.monomorphisms _)
  (hfib : simplicial.categoryWithFibrations.fibrations = SSet.modelCategoryQuillen.J.{vC}.rlp)
  {D : Type uD} [Category.{vD} D] [target : ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (hF : @Quillen.IsLeftQuillen C _ D _ original.categoryWithCofibrations
    original.categoryWithWeakEquivalences target.categoryWithCofibrations
    target.categoryWithWeakEquivalences L)

-- The target model and its Hom universe are arbitrary; no target functorial replacement is input.
example : @Quillen.IsLeftQuillen C _ D _ m.categoryWithCofibrations
      m.categoryWithWeakEquivalences target.categoryWithCofibrations
      target.categoryWithWeakEquivalences L ↔
    ∀ (Y : D), IsFibrant Y → @Bousfield.localObjects C _ original simplicial cof fib S (R.obj Y) :=
  by
    let := original
    exact h.leftQuillen_iff_rightAdjoint_local hcof hfib adj hF
end Localization

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Quillen.FibrantTesting,
    `SerrePositivity.HomotopicalAlgebra.Quillen.FibrantCriterion,
    `SerrePositivity.HomotopicalAlgebra.Localization.QuillenCriterion]
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
  logInfo m!"Quillen fibrant criterion audit passed: {count} declarations in {seen.size} modules."
