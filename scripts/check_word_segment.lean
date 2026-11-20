import SerrePositivity.HomotopicalAlgebra.Simplicial.WordSegmentComparison

universe u v w m uH vH
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open SerrePositivity.SimplicialModel

section Algebra
open SegmentWords
variable {A : Type u} {B : Type v} {D : Type w} {e z : A} {eB zB : B} {eD zD : D}
example : Type u := Word A e z
example : letter e z e = 1 := letter_unit e z
example (h : e ≠ z) : letter e z z = 0 := letter_zero e z h
example {M : Type m} [MonoidWithZero M] (f : A → M) (he : f e = 1) (hz : f z = 0) (a : A) :
    lift e z f (letter e z a) = f a := lift_letter e z f he hz a
example (hB : eB ≠ zB) (hD : eD ≠ zD) (f : A → B) (g : B → D)
    (he : f e = eB) (hz : f z = zB) (he' : g eB = eD) (hz' : g zB = zD) :
    (map (g ∘ f) : Word A e z →*₀ Word D eD zD) =
      (map (e := eB) (z := zB) (eB := eD) (zB := zD) g).comp
        (map (eB := eB) (zB := zB) f) := map_comp hB hD f g he hz he' hz'
end Algebra

section Simplicial
open WordSegment
example : SSet.{v} := obj
example (n : SimplexCategoryᵒᵖ) : endpoint.{v} n 0 ≠ endpoint n 1 := endpoint_ne n
example : SSet.stdSimplex.δ (1 : Fin 2) ≫ letter.{v} = unit := vertex_zero_letter
example : SSet.stdSimplex.δ (0 : Fin 2) ≫ letter.{v} = zero := vertex_one_letter
example : unit.{v} ≠ zero := unit_ne_zero
example : mul.{v} ▷ obj ≫ mul = (α_ obj obj obj).hom ≫ obj ◁ mul ≫ mul := mul_assoc
example {T : SSet.{v}} (a : T ⟶ obj) :
    CategoryTheory.CartesianMonoidalCategory.lift a (unitAt T) ≫ mul = a := mul_unitAt a
example {T : SSet.{v}} (a : T ⟶ obj) :
    CategoryTheory.CartesianMonoidalCategory.lift (zeroAt T) a ≫ mul = zeroAt T := zeroAt_mul a
example : SSet.Homotopy (𝟙 obj.{v}) (zeroAt obj) := contraction
end Simplicial

section Comparison
open WordSegment WordSegmentComparison
variable {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)
example : IsIso (L.map projection) := projection_isIso L hL
example : IsIso (L.map letter) := letter_isIso L hL
example : IsIso (AnodyneHomotopy.anodyneQ.map letter.{v}) := localized_letter_isIso
end Comparison

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[`SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.SegmentWords,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.WordSegment,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.WordSegmentComparison]
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
    throwError "Missing finite-word segment modules"
  logInfo m!"Word segment audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
