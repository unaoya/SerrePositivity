import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u vH uH
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.ModelReplacement

section ArbitraryModelSource
variable {C : Type u} [Category.{v} C] [ModelCategory C]
example (n : SimplexCategoryᵒᵖ) :
    DualResolutionTargets.presentation C n ⋙ FibrantReplacementObject.projection =
      DualResolutionTargets.base C := DualResolutionTargets.presentation_projection C n
example (Y : DualResolutionTargets.Index C) (n : SimplexCategoryᵒᵖ) :
    IsFibrant ((DualResolutionTargets.diagram C Y).obj n) :=
  DualResolutionTargets.isFibrant_obj C Y n
example {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (Y : DualResolutionTargets.Index C) :
    weakEquivalences C (((DualResolutionTargets.presentations C).map f).app Y).map :=
  DualResolutionTargets.operator_weakEquivalence C f Y
example : (DualResolutionTargets.framedBase C).Full := inferInstance
example (X : ReplacementMapping.Index C) :
    (RightResolutionRefinement.original C).obj (RightResolutionRefinement.ofOriginal C X) = X :=
  RightResolutionRefinement.ofOriginal_original C X

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
-- Source object and Hom universes are independent; values stay in the Hom universe.
example : RightResolutionMapping.Index C ⥤ SSet.{v} :=
  RightResolutionMapping.kanFunctor hcof hfib
example (X : RightResolutionMapping.Index C) :
    SSet.KanComplex ((RightResolutionMapping.kanFunctor hcof hfib).obj X) :=
  RightResolutionMapping.kanComplex hcof hfib X
example {X Y : RightResolutionMapping.Index C} (f : X ⟶ Y)
    (hs : weakEquivalences C f.1.unop.map.base)
    (ht : weakEquivalences C ((RightResolutionMapping.projection (C := C)).map f).2) :
    weakEquivalences SSet.{v} ((RightResolutionMapping.kanFunctor hcof hfib).map f) :=
  RightResolutionMapping.kanFunctor_map_weakEquivalence hcof hfib f hs ht
example : RightResolutionRefinement.middle C hcof hfib ⟶
    RightResolutionRefinement.original C ⋙ ReplacementMapping.uncurried hcof hfib :=
  RightResolutionRefinement.left C hcof hfib
example (X : RightResolutionRefinement.Index C) :
    weakEquivalences SSet.{v} ((RightResolutionRefinement.left C hcof hfib).app X) ∧
      weakEquivalences SSet.{v} ((RightResolutionRefinement.kanRight C hcof hfib).app X) :=
  ⟨RightResolutionRefinement.left_weakEquivalence C hcof hfib X,
    RightResolutionRefinement.kanRight_weakEquivalence C hcof hfib X⟩
example (X : RightResolutionMapping.Index C) :
    Function.Bijective (SSet.mapπ₀ ((RightResolutionMapping.kanComparison hcof hfib).app X)) :=
  RightResolutionMapping.kanComparison_piZero_bijective hcof hfib X

variable {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
  [Q.IsLocalization (weakEquivalences C)]
-- The new Kan value over every original presentation has the original base Hom.
example (X : ReplacementMapping.Index C) :
    SSet.π₀ ((RightResolutionMapping.kanFunctor hcof hfib).obj
      ((RightResolutionRefinement.resolved C).obj
        (RightResolutionRefinement.ofOriginal C X))) ≃
      (Q.obj X.1.unop.inner.base ⟶ Q.obj X.2.base) :=
  RightResolutionMapping.piZeroEquiv hcof hfib Q _
end ArbitraryModelSource

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.DualResolutionTargets,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.RightResolutionMapping,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.RightResolutionRefinement]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  unless modules.size == expected.size do
    throwError "Some right resolution mapping modules were not audited"
  logInfo m!"Right resolution mapping audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
