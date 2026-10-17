import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u uD vD
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {D : Type uD} [Category.{vD} D] (L : SSet.{max u v} ⥤ D)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

-- All input universes remain independent. There is no large simplicial model.
example : (RightResolutionMapping.zero (C := C) hcof hfib ⋙
    SSet.uliftFunctor.{max u v, v}) ⋙ L ≅
    (RightResolutionMapping.projection ⋙ OrdinaryResolutionBar.functor) ⋙ L :=
  OrdinaryBarMappingComparison.zeroIso hcof hfib L hL

-- An arbitrary base weak equivalence is inverted, without a functorial section.
include hcof hfib hL in
example {X Y : Cᵒᵖ × C} (f : X ⟶ Y)
    (hs : weakEquivalences C f.1.unop) (ht : weakEquivalences C f.2) :
    IsIso (L.map (OrdinaryResolutionBar.functor.map f)) :=
  OrdinaryBarBaseInvariance.map_isIso hcof hfib L hL f hs ht

-- The entire original diagram compares over the full refinement category.
example :
    ((RightResolutionRefinement.original C ⋙ ReplacementMapping.uncurried hcof hfib) ⋙
      SSet.uliftFunctor.{max u v, v}) ⋙ L ≅
    ((RightResolutionRefinement.original C ⋙ ReplacementMapping.projection) ⋙
      OrdinaryResolutionBar.functor) ⋙ L :=
  OrdinaryBarReplacementComparison.refinementIso hcof hfib L hL

-- Every original presentation occurs with its original value and base.
example (X : ReplacementMapping.Index C) :
    L.obj (SSet.uliftFunctor.{max u v, v}.obj
      ((ReplacementMapping.uncurried hcof hfib).obj X)) ≅
    L.obj (OrdinaryResolutionBar.functor.obj (ReplacementMapping.projection.obj X)) :=
  OrdinaryBarReplacementComparison.presentationIso hcof hfib L hL X

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarMappingComparison,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarBaseInvariance,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarReplacementComparison]
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
    throwError "Missing ordinary bar mapping comparison modules"
  logInfo m!"Ordinary bar mapping comparison audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
