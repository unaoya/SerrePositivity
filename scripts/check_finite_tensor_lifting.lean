import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TensorKanCriterion
import Lean.Util.CollectAxioms

noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex
open scoped SSet.modelCategoryQuillen

variable {C : Type u} [Category.{v} C] [HasFiniteColimits C]
  (A : SimplexCategory ⥤ C)

-- All actual horns and boundaries, including dimension zero, have finite tensors.
example (n : ℕ) (i : Fin (n + 1)) :
    HasColimit (SubcomplexTensor.diagram (SSet.horn.{v} n i) ⋙ A) := inferInstance

example (n : ℕ) :
    HasColimit (SubcomplexTensor.diagram (SSet.boundary.{v} n) ⋙ A) := inferInstance

example (n : ℕ) (i : Fin (n + 1)) (Y : C) :
    ((SSet.horn.{v} n i).toSSet ⟶ (cosimplicialHom A).obj Y) ≃
      (SubcomplexTensor.obj (SSet.horn.{v} n i) A ⟶ Y) :=
  SubcomplexTensor.homEquiv _ A Y

example (n : ℕ) (Y : C) :
    ((SSet.boundary.{v} n).toSSet ⟶ (cosimplicialHom A).obj Y) ≃
      (SubcomplexTensor.obj (SSet.boundary.{v} n) A ⟶ Y) :=
  SubcomplexTensor.homEquiv _ A Y

example (n : ℕ) (i : Fin (n + 1)) {Y Z : C} (p : Y ⟶ Z)
    [HasLiftingProperty (SubcomplexTensor.inclusion (SSet.horn.{v} n i) A) p] :
    HasLiftingProperty (SSet.horn.{v} n i).ι ((cosimplicialHom A).map p) :=
  SubcomplexTensor.hasLiftingProperty _ A p

-- Conditional Kan reduction, not a test asserting the missing frame tensor theorem.
example [ModelCategory C]
    (hA : ∀ (n : ℕ) (i : Fin (n + 2)), trivialCofibrations C
      (SubcomplexTensor.inclusion (SSet.horn.{v} (n + 1) i) A))
    (Y : C) [IsFibrant Y] : SSet.KanComplex ((cosimplicialHom A).obj Y) :=
  kanComplex_of_hornTensors A hA Y

example [ModelCategory C]
    (hA : ∀ n : ℕ, cofibrations C (SubcomplexTensor.inclusion (SSet.boundary.{v} n) A))
    {Y Z : C} (p : Y ⟶ Z) [Fibration p] [WeakEquivalence p] (n : ℕ) :
    HasLiftingProperty (SSet.boundary.{v} n).ι ((cosimplicialHom A).map p) :=
  boundary_lifting_of_cofibration A hA p n

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.PresentationHom,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.PresentationLifting,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.NonsingularPresentation,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SubcomplexTensor,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TensorKanCriterion]
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
  logInfo m!"Finite tensor lifting audit passed: {count} declarations in {seen.size} modules."
