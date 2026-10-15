import SerrePositivity.HomotopicalAlgebra.Localization.UniversalProperty
import Lean.Util.CollectAxioms

noncomputable section
universe vC uC vD uD vHC uHC vHD uHD
open CategoryTheory HomotopicalAlgebra
open SerrePositivity

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


  [ModelCategory SSet.{vD}] [ModelCategory SSet.{max vC vD}]
  (hcofD : cofibrations SSet.{vD} = MorphismProperty.monomorphisms _)
  (hfibD : fibrations SSet.{vD} = SSet.modelCategoryQuillen.J.{vD}.rlp)
  (hcofB : cofibrations SSet.{max vC vD} = MorphismProperty.monomorphisms _)
  (hfibB : fibrations SSet.{max vC vD} = SSet.modelCategoryQuillen.J.{max vC vD}.rlp)

-- No cofibrancy of endpoints of S, or properness, tractability or target factorization is assumed.
example : @Quillen.IsLeftQuillen C _ D _ m.categoryWithCofibrations
      m.categoryWithWeakEquivalences target.categoryWithCofibrations
      target.categoryWithWeakEquivalences L ↔
    ∀ {X Z : C} (f : X ⟶ Z), S f → weakEquivalences D
      (L.map ((@HomotopyFunctionComplex.cofibrantSource C _ original cof).map f)) := by
  let := original
  exact h.leftQuillen_iff_cofibrant_test hcof hfib adj hF hcofD hfibD hcofB hfibB

example (cof' : MorphismProperty.FunctorialFactorizationData
      original.categoryWithCofibrations.cofibrations
      (original.categoryWithFibrations.fibrations ⊓
        original.categoryWithWeakEquivalences.weakEquivalences))
    (fib' : MorphismProperty.FunctorialFactorizationData
      (original.categoryWithCofibrations.cofibrations ⊓
        original.categoryWithWeakEquivalences.weakEquivalences)
      original.categoryWithFibrations.fibrations) :
    let := original
    (∀ {X Z : C} (f : X ⟶ Z), S f → weakEquivalences D
      (L.map ((HomotopyFunctionComplex.cofibrantSource cof).map f))) ↔
    (∀ {X Z : C} (f : X ⟶ Z), S f → weakEquivalences D
      (L.map ((HomotopyFunctionComplex.cofibrantSource cof').map f))) := by
  let := original
  exact h.cofibrant_test_choices_iff hcof hfib adj hF hcofD hfibD hcofB hfibB cof' fib'

-- The final statement uses any actual left derived functor and arbitrary localization universes.
example {HC : Type uHC} [Category.{vHC} HC] {HD : Type uHD} [Category.{vHD} HD]
    (QC : C ⥤ HC) [QC.IsLocalization original.categoryWithWeakEquivalences.weakEquivalences]
    (QD : D ⥤ HD) [QD.IsLocalization (weakEquivalences D)]
    {LF : HC ⥤ HD} (α : QC ⋙ LF ⟶ L ⋙ QD)
    [LF.IsLeftDerivedFunctor α original.categoryWithWeakEquivalences.weakEquivalences] :
    @Quillen.IsLeftQuillen C _ D _ m.categoryWithCofibrations
      m.categoryWithWeakEquivalences target.categoryWithCofibrations
      target.categoryWithWeakEquivalences L ↔
    ∀ {X Z : C} (f : X ⟶ Z), S f → IsIso (LF.map (QC.map f)) := by
  let := original
  exact h.leftQuillen_iff_derived_inverts hcof hfib adj hF hcofD hfibD hcofB hfibB QC QD α

end Localization

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.AdjunctionWeakEquivalence,
    `SerrePositivity.HomotopicalAlgebra.Localization.FibrantMappingTests,
    `SerrePositivity.HomotopicalAlgebra.Localization.QuillenLocalObjects,
    `SerrePositivity.HomotopicalAlgebra.Localization.UniversalProperty,
    `SerrePositivity.HomotopicalAlgebra.Quillen.DerivedMapTest]
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
  logInfo m!"Localization Quillen universal property audit passed: {count} declarations in {seen.size} modules."
