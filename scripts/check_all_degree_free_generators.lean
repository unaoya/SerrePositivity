import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorCategories

universe v u vA vB vD vK
noncomputable section
open CategoryTheory
open SerrePositivity SerrePositivity.HomotopyFunctionComplex

-- Arbitrary edge-map intersections, with independent Hom universes and all vertices retained.
section Paths
variable {V : Type u} {A : Quiver.{vA} V} {B : Quiver.{vB} V}
  {D : Quiver.{vD} V} {K : Quiver.{vK} V}
  (f : QuiverPaths.EdgeMap A D) (g : QuiverPaths.EdgeMap B D)
  (a : QuiverPaths.EdgeMap K A) (b : QuiverPaths.EdgeMap K B)
  (h : ∀ {X Y} (x : @Quiver.Hom V A X Y) (y : @Quiver.Hom V B X Y), f x = g y →
    ∃ z : @Quiver.Hom V K X Y, a z = x ∧ b z = y)
example {X Y : V} (p : @Quiver.Path V A X Y) (q : @Quiver.Path V B X Y)
    (hpq : QuiverPaths.mapPath f p = QuiverPaths.mapPath g q) :
    ∃ r : @Quiver.Path V K X Y, QuiverPaths.mapPath a r = p ∧ QuiverPaths.mapPath b r = q :=
  QuiverPaths.mapPath_intersection f g a b h p q hpq
end Paths

-- All n and i <= j, on iterated free generators of an arbitrary quiver, without a model.
section Generators
variable {V : Type u} [Quiver.{v} V] {X Y : V}
open FreeGeneratorDegeneracies
example (n : ℕ) (i : Fin (n + 1)) :
    Function.Injective (degeneracy (V := V) n i (X := X) (Y := Y)) := degeneracy_injective n i
example (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) (p q : hom n.succ X Y) :
    degeneracy (n + 1) i.castSucc p = degeneracy (n + 1) j.succ q ↔
      ∃ r : hom n X Y, p = degeneracy n j r ∧ q = degeneracy n i r :=
  degeneracy_intersection_iff n i j h p q
example (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) (p q : hom n.succ X Y)
    (hpq : degeneracy (n + 1) i.castSucc p = degeneracy (n + 1) j.succ q) :
    ∃! r : hom n X Y, p = degeneracy n j r ∧ q = degeneracy n i r :=
  degeneracy_intersection_unique n i j h p q hpq
end Generators

-- The explicit degree categories and degeneracy functors agree with the actual comonad powers.
section Categories
variable (C : Type u) [Category.{v} C]
open FreeGeneratorCategories FreeGeneratorDegeneracies
example (n : ℕ) : degree C n =
    ComonadResolutionOperators.power FreePathResolution.comonad
      (FreePathResolutionPresentation.base C) n := degree_power C n
example (n : ℕ) (i : Fin (n + 1)) :
    (degeneracyFunctor C n i).toCatHom ≫ eqToHom (degree_power C (n + 2)) =
      eqToHom (degree_power C (n + 1)) ≫
        ComonadResolutionOperators.degeneracy FreePathResolution.comonad
          (FreePathResolutionPresentation.base C) n i := degeneracy_comparison C n i
example (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) {X Y : C} (p q : hom (n + 1) X Y) :
    (degeneracyFunctor C (n + 1) i.castSucc).map (singleton (n + 1) p) =
      (degeneracyFunctor C (n + 1) j.succ).map (singleton (n + 1) q) ↔
        ∃ r : hom n X Y, p = degeneracy n j r ∧ q = degeneracy n i r :=
  generator_image_intersection C n i j h p q
end Categories

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.CategoryTheory.Quiver.PathIntersections,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorDegeneracies,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorCategories]
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
    throwError "Missing all-degree free generator modules"
  logInfo m!"All-degree free generator audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
