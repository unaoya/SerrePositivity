import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Lifting
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexFinite
import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Lean.Util.CollectAxioms

universe v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

section General
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ) {C : Type u'} [Category.{v'} C]
  [∀ j, HasColimitsOfShape (LatchingIndex r j) C]
  [∀ j, HasLimitsOfShape (MatchingIndex r j) C] [HasPushouts C] [HasPullbacks C]
  {A B X Y : J ⥤ C} {i : A ⟶ B} {p : X ⟶ Y}
  [∀ j, HasLiftingProperty (relativeLatchingMap r j i) (relativeMatchingMap r j p)]

include r

example : HasLiftingProperty i p := Lifting.hasLiftingProperty r

example {a : A ⟶ X} {b : B ⟶ Y} (sq : CommSq a i p b) :
    ∃ l : B ⟶ X, i ≫ l = a ∧ l ≫ p = b :=
  ⟨Lifting.lift r sq, Lifting.fac_left r sq, Lifting.fac_right r sq⟩

example {a : A ⟶ X} {b : B ⟶ Y} (sq : CommSq a i p b) (n : ℕ)
    (j : J) (hj : r.deg j < n) :
    (Lifting.tower r sq n).successor.hom.app ⟨j, lt_trans hj (Nat.lt_succ_self n)⟩ =
      (Lifting.tower r sq n).hom.app ⟨j, hj⟩ :=
  LiftBelow.successor_app_old _ j hj
end General

section Model
variable {C : Type u'} [Category.{v'} C] [ModelCategory C]

example {A B X Y : SimplexCategory ⥤ C} (i : A ⟶ B) (p : X ⟶ Y)
    [∀ j, Cofibration (relativeLatchingMap simplex j i)]
    [∀ j, Fibration (relativeMatchingMap simplex j p)]
    [∀ j, WeakEquivalence (relativeMatchingMap simplex j p)] : HasLiftingProperty i p := by
  have : ∀ j, HasColimitsOfShape (LatchingIndex simplex j) C := fun j ↦ inferInstance
  have : ∀ j, HasLimitsOfShape (MatchingIndex simplex j) C := fun j ↦ inferInstance
  have : ∀ j, HasLiftingProperty (relativeLatchingMap simplex j i)
      (relativeMatchingMap simplex j p) := fun j ↦ inferInstance
  exact Lifting.hasLiftingProperty simplex

example {A B X Y : SimplexCategoryᵒᵖ ⥤ C} (i : A ⟶ B) (p : X ⟶ Y)
    [∀ j, Cofibration (relativeLatchingMap simplexOp j i)]
    [∀ j, WeakEquivalence (relativeLatchingMap simplexOp j i)]
    [∀ j, Fibration (relativeMatchingMap simplexOp j p)] : HasLiftingProperty i p := by
  have : ∀ j, HasColimitsOfShape (LatchingIndex simplexOp j) C := fun j ↦ inferInstance
  have : ∀ j, HasLimitsOfShape (MatchingIndex simplexOp j) C := fun j ↦ inferInstance
  have : ∀ j, HasLiftingProperty (relativeLatchingMap simplexOp j i)
      (relativeMatchingMap simplexOp j p) := fun j ↦ inferInstance
  exact Lifting.hasLiftingProperty simplexOp
end Model

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.LowerNaturality,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.LiftBelow,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.LiftSuccessor,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Lifting]
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
  if modules.size != expected.size then throwError "Not all Reedy lifting induction modules were audited"
  logInfo m!"Reedy lifting induction audit passed: {count} declarations in 4 modules, standard axioms only."
