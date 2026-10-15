import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SourceInvariance
import Lean.Util.CollectAxioms

noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.Reedy
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

-- Arbitrary ordinary resolutions and objectwise equivalences between them.
example (X X' : C) (q : CofibrantResolution simplex X) (q' : CofibrantResolution simplex X')
    (α : q.obj ⟶ q'.obj) (hα : ∀ n, weakEquivalences C (α.app n))
    (Y : C) [IsFibrant Y] :
    weakEquivalences SSet.{v} ((cosimplicialHomMap α).app Y) :=
  cosimplicialHomMap_weakEquivalence hcof α q.cofibrant q'.cofibrant hα Y

-- The relative boundary theorem applies to all positive and zero dimensions.
example {A B : SimplexCategory ⥤ C} (α : A ⟶ B)
    (hα : reedyLeft simplex (trivialCofibrations C) α) (Y : C) [IsFibrant Y] :
    trivialFibrations SSet.{v} ((cosimplicialHomMap α).app Y) :=
  cosimplicialHomMap_trivialFibration hcof α hα Y

-- This is the actual mixed source/target map of the constructed strict bifunctor.
example (hw : weakEquivalences SSet.{v} = SerrePositivity.SimplicialHomotopy.weakEquivalences)
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    {X X' : Cᵒᵖ} (f : X ⟶ X') (hf : weakEquivalences C f.unop)
    {Y Y' : C} (g : Y ⟶ Y') (hg : weakEquivalences C g) :
    SerrePositivity.SimplicialHomotopy.weakEquivalences
      (((chosenResolutionHom cof fib).map f).app Y ≫
        ((chosenResolutionHom cof fib).obj X').map g) :=
  chosenResolutionHom_map_both_geometricWeakEquivalence hcof hw cof fib f hf g hg

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.PresentationSourceLifting,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.RelativeBoundaryTensor,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SourceInvariance]
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
  logInfo m!"Resolution Hom source invariance audit passed: {count} declarations in {seen.size} modules."
