import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.AccessibleBoundary
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexResolution
import Lean.Util.CollectAxioms

noncomputable section
universe w s t v u v' u'
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

-- The right-adjoint theorem works in accessible categories without model
-- structures or pre-assumed accessibility of the adjoint functor.
example {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    [IsAccessibleCategory.{w} C] [IsAccessibleCategory.{w} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) : G.IsAccessible.{w} :=
  SerrePositivity.Smith.AccessibleAdjunction.rightAdjoint_isAccessible adj

-- Neither the shape's object universe nor its morphism universe is forced
-- to coincide with the accessibility universe.
example {C : Type u} [Category.{v} C] [IsLocallyPresentable.{w} C] [HasPullbacks C]
    (K : Type t) [Category.{s} K] [EssentiallySmall.{w} K] [HasLimitsOfShape K C] :
    (lim : (K ⥤ C) ⥤ C).IsAccessible.{w} :=
  SerrePositivity.Smith.AccessibleLimits.limitFunctor_isAccessible K

-- Actual pullback limits are included.
example {C : Type u} [Category.{v} C] [IsLocallyPresentable.{w} C] [HasPullbacks C] :
    (lim : (WalkingCospan ⥤ C) ⥤ C).IsAccessible.{w} :=
  SerrePositivity.Smith.AccessibleLimits.limitFunctor_isAccessible.{w} (C := C) WalkingCospan

variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]

-- All shape/limit/smallness hypotheses are discharged for the actual Δ and
-- Δop Reedy structures, rather than assumed on their matching functors.
example : ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular), ∀ n,
    (lowerLatchingEvaluation (C := C) simplex n).IsCardinalAccessible κ ∧
    (lowerMatchingEvaluation (C := C) simplex n).IsCardinalAccessible κ :=
  exists_common_boundary_accessibility.{w} (C := C) simplex

example : ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular), ∀ n,
    (lowerLatchingEvaluation (C := C) simplexOp n).IsCardinalAccessible κ ∧
    (lowerMatchingEvaluation (C := C) simplexOp n).IsCardinalAccessible κ :=
  exists_common_boundary_accessibility.{w} (C := C) simplexOp

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Smith.AccessibleAdjunction,
    `SerrePositivity.HomotopicalAlgebra.Smith.AccessibleLimits,
    `SerrePositivity.HomotopicalAlgebra.Smith.AccessibleFamilies,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.AccessibleBoundary]
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
  logInfo m!"Accessible Reedy boundary audit passed: {count} declarations in {seen.size} modules."
