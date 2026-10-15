import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.HornTensor
import Lean.Util.CollectAxioms

noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.Reedy
open scoped SSet.modelCategoryQuillen
variable {C : Type u} [Category.{v} C] [ModelCategory C]

-- No functorial factorization hypothesis for the ordinary resolution.
example (X Y : C) [IsFibrant Y] :
    SSet.KanComplex ((cosimplicialHom (cosimplicialResolution X).obj).obj Y) :=
  cosimplicialResolution_hom_kanComplex X Y

-- All horns in every positive dimension, including the outer horns.
example (X : C) (n : ℕ) (i : Fin (n + 2)) :
    trivialCofibrations C (SubcomplexTensor.inclusion (SSet.horn.{v} (n + 1) i)
      (cosimplicialResolution X).obj) :=
  hornTensor_trivialCofibration _ (cosimplicialResolution X).cofibrant
    (cosimplicialResolution X).homotopicallyConstant n i

example (X : C) {Y Z : C} (p : Y ⟶ Z) [Fibration p] :
    Fibration ((cosimplicialHom (cosimplicialResolution X).obj).map p) :=
  cosimplicialHom_fibration _ (cosimplicialResolution X).cofibrant
    (cosimplicialResolution X).homotopicallyConstant p

-- The actual strict bifunctor also takes values in Kan complexes when
-- chosen source factorization data are supplied explicitly.
example
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (X : Cᵒᵖ) (Y : C) : SSet.KanComplex (((chosenResolutionHom cof fib).obj X).obj Y) :=
  chosenResolutionHom_kanComplex cof fib X Y

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorWeakEquivalence,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.HornTensor]
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
  logInfo m!"Resolution Hom Kan audit passed: {count} declarations in {seen.size} modules."
