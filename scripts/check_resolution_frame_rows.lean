import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.HomotopyFunctionComplex

variable {C : Type u} [Category.{v} C] [ModelCategory C]

-- The row is a genuine resolution of the same original base, at independent u and v.
example (X : ResolutionObject C) (n : SimplexCategory) :
    (ResolutionFrameRows.row X n).base = X.base := rfl

example (X : ResolutionObject C) (n : SimplexCategory) :
    (ResolutionFrameRows.augmentation X n).base = 𝟙 X.base :=
  ResolutionFrameRows.augmentation_base X n

example (X : ResolutionObject C) {n m : SimplexCategory} (θ : n ⟶ m) :
    ResolutionFrameRows.rowMap X θ ≫ ResolutionFrameRows.augmentation X m =
      ResolutionFrameRows.augmentation X n ≫ 𝟙 X :=
  (ResolutionFrameRows.comparison X).naturality θ

-- All actual framed comparison maps, not a newly assumed functorial choice, control the rows.
example {X Y : FramedResolution C} (f : X ⟶ Y) :
    ResolutionFrameRowFunctor.map f ≫ ResolutionFrameRows.comparison Y.inner =
      ResolutionFrameRows.comparison X.inner ≫ (Functor.const SimplexCategory).map f.map :=
  ResolutionFrameRowFunctor.comparison.naturality f

example : ResolutionRowMixedMapping.diagonal (C := C) ≅ MixedResolutionComparison.output :=
  ResolutionRowMixedMapping.diagonalIso

-- This is an actual arrow in the existing bar's degreewise element comma category.
example (R : RightResolutionMapping.Index C) (n m : SimplexCategoryᵒᵖ)
    (x : ((MixedBiresolutionComparison.functor (C := C)).obj R).obj m) :
    ResolutionBarReference.point R m x ⟶ ResolutionBarRowPresentations.element R n m x :=
  ResolutionBarRowPresentations.elementArrow R n m x

example (R : RightResolutionMapping.Index C) (n : SimplexCategoryᵒᵖ) :
    (MixedBiresolutionComparison.functor (C := C)).map
        (ResolutionBarRowPresentations.arrow R n) =
      (ResolutionRowMixedMapping.rowComparison n).app R :=
  ResolutionBarRowPresentations.arrow_raw R n

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

example (R : RightResolutionMapping.Index C) (n : SimplexCategoryᵒᵖ) :
    weakEquivalences SSet.{v} ((ResolutionRowMixedMapping.rowComparison n).app R) :=
  ResolutionRowMixedMapping.rowComparison_weakEquivalence hcof hfib R n

example (R : RightResolutionMapping.Index C) {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    weakEquivalences SSet.{v} ((ResolutionRowMixedMapping.rows.map θ).app R) :=
  ResolutionRowMixedMapping.row_operator_weakEquivalence hcof hfib R θ

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionFrameRows,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionFrameRowFunctor,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.MixedHomBifunctor,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionRowMixedMapping,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowPresentations]
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
    throwError "Some resolution frame row modules were not audited"
  logInfo m!"Resolution frame row audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
