import SerrePositivity.HomotopicalAlgebra.Localization.EnrichedDetection
import Lean.Util.CollectAxioms

noncomputable section
universe vV uV vC uC
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.MonoidalCategory
open SerrePositivity SerrePositivity.Bousfield

section General
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [base : ModelCategory V]
  {C : Type uC} [Category.{vC} C] [original : ModelCategory C]
  [EnrichedOrdinaryCategory V C] [simplicial : ModelCategory SSet.{vC}]
  [ModelCategory SSet.{vV}] [ModelCategory SSet.{max vC vV}]
  {cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)}
  {fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C)}
  {S : MorphismProperty C} {m : ModelCategory C}
  (h : @IsLocalizationModel C _ original simplicial cof fib S m)
  (hcofC : simplicial.categoryWithCofibrations.cofibrations = MorphismProperty.monomorphisms _)
  (hfibC : simplicial.categoryWithFibrations.fibrations = SSet.modelCategoryQuillen.J.{vC}.rlp)
  (P : SerrePositivity.Enriched.TensorCotensor V C)
  (hP : @Quillen.IsQuillenBifunctor V _ base C _ original C _ original P.tensor)
  (hPn : @Quillen.IsQuillenBifunctor V _ base C _ m C _ m P.tensor)
  (hunit : let := original; SerrePositivity.Enriched.HasTensorUnitAxiom P)
  (cofV : MorphismProperty.FunctorialFactorizationData (cofibrations V) (trivialFibrations V))
  (hcofV : cofibrations SSet.{vV} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{vV} = SSet.modelCategoryQuillen.J.{vV}.rlp)
  (hcofB : cofibrations SSet.{max vC vV} = MorphismProperty.monomorphisms _)
  (hfibB : fibrations SSet.{max vC vV} = SSet.modelCategoryQuillen.J.{max vC vV}.rlp)


-- V and C have independent object and Hom universes; the unit may be noncofibrant.
example : let := original
    localObjects.{vC, uC} (C := C) cof fib S =
      SerrePositivity.Enriched.localObjects (V := V) cof fib S := by
  let := original
  exact h.localObjects_eq_enriched (V := V) hcofC hfibC P hP hPn hunit cofV
    hcofV hfibV hcofB hfibB

example : let := original
    localEquivalences.{vC, uC} (C := C) cof fib S =
      SerrePositivity.Enriched.localEquivalences (V := V) cof fib S := by
  let := original
  exact h.localEquivalences_eq_enriched (V := V) hcofC hfibC P hP hPn hunit cofV
    hcofV hfibV hcofB hfibB

example (Y : C) : let := original
    m.categoryWithFibrations.fibrations (terminal.from Y) ↔ IsFibrant Y ∧
      SerrePositivity.Enriched.localObjects (V := V) cof fib S Y := by
  let := original
  exact h.fibrant_iff_enriched (V := V) hcofC hfibC P hP hPn hunit cofV
    hcofV hfibV hcofB hfibB Y
end General

section SimplicialUnit
variable {D : Type uC} [Category.{vC} D] [ModelCategory D]
  [ModelCategory SSet.{vC}] [EnrichedOrdinaryCategory SSet.{vC} D]

-- In the simplicial specialization the action unit axiom is supplied by its identity replacement.
example (P : SerrePositivity.Enriched.TensorCotensor SSet.{vC} D)
    (hcof : cofibrations SSet.{vC} = MorphismProperty.monomorphisms _) :
    SerrePositivity.Enriched.HasTensorUnitAxiom P := by
  have : IsCofibrant (𝟙_ SSet.{vC}) := by
    constructor
    rw [hcof]
    exact inferInstanceAs (Mono _)
  exact SerrePositivity.Enriched.tensorUnitAxiom_of_cofibrant_unit P
end SimplicialUnit

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Monoidal.PullbackHomSource,
    `SerrePositivity.HomotopicalAlgebra.Enriched.DerivedMapping,
    `SerrePositivity.HomotopicalAlgebra.Enriched.UnitAxiom,
    `SerrePositivity.HomotopicalAlgebra.Enriched.UnitFrame,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.EnrichedTensorFrameHom,
    `SerrePositivity.HomotopicalAlgebra.Localization.EnrichedLocalObjects,
    `SerrePositivity.HomotopicalAlgebra.Localization.FrameTests,
    `SerrePositivity.HomotopicalAlgebra.Localization.EnrichedTestComparison,
    `SerrePositivity.HomotopicalAlgebra.Localization.EnrichedDetection]
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
  logInfo m!"Enriched local-object detection audit passed: {count} declarations in {seen.size} modules."
