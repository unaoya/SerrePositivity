import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeDegeneracyExtension
import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryGluing
import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeBoundaryGluing

universe v u w vD uD vV uV
noncomputable section
open CategoryTheory
open SerrePositivity.HomotopyFunctionComplex

-- Arbitrary targets, every degree, every pair of indices, including equal indices.
section Values
open FreeGeneratorDegeneracies FreeGeneratorLatchingValues
variable {V : Type u} [Quiver.{v} V] {X Y : V} (n : ℕ) {T : Sort w}
  (value : Fin (n + 2) → hom (n + 1) X Y → T) (h : Compatible n value)
example (i j : Fin (n + 2)) (p q : hom (n + 1) X Y)
    (hpq : degeneracy (n + 1) i p = degeneracy (n + 1) j q) : value i p = value j q :=
  values_agree n value h i j p q hpq
example (i : Fin (n + 2)) (p : hom (n + 1) X Y) :
    desc n value (degeneracy (n + 1) i p) (fixed_degeneracy n i p) = value i p :=
  desc_degeneracy n value h i p _
example (f : (e : hom (n + 2) X Y) → Fixed n e → T)
    (hf : ∀ i p he, f (degeneracy (n + 1) i p) he = value i p)
    (e : hom (n + 2) X Y) (he : Fixed n e) : f e he = desc n value e he :=
  desc_unique n value h f hf e he
end Values

section Extension
open FreeGeneratorCategories FreeGeneratorDegeneracies OrdinaryBarFreeDegeneracyExtension
open OrdinaryBarFreeDiagramExtension
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (D : Type uD) [Category.{vD} D] (n : ℕ)
  {T U : SSet.{max u v}} (j : U ⟶ T) [Mono j]
  (φ : degree D (n + 2) ⥤q target (C := C) hcof hfib U)
  (value : Value hcof hfib D n φ)
  (compatible : ∀ X Y : D, FreeGeneratorLatchingValues.Compatible n
    (fun i (p : hom (n + 1) X Y) => value i p))
  (restriction : ∀ (i : Fin (n + 2)) {X Y : D} (p : hom (n + 1) X Y),
    (OrdinaryBarChoiceCategory.reindex hcof hfib j).map (value i p) =
      φ.map (degeneracy (n + 1) i p))
example : filler hcof hfib D n j φ value restriction ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib j =
      Paths.lift (V := degree D (n + 2)) φ :=
  filler_boundary hcof hfib D n j φ value restriction
example : filler hcof hfib D n j φ value restriction ⋙
    OrdinaryBarChoiceCategory.projection hcof hfib T =
      Paths.lift (V := degree D (n + 2)) φ ⋙
        OrdinaryBarChoiceCategory.projection hcof hfib U :=
  filler_projection hcof hfib D n j φ value restriction
example (i : Fin (n + 2)) : degenerateDiagram hcof hfib D n φ value i ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib j =
      degeneracyFunctor D (n + 1) i ⋙ Paths.lift (V := degree D (n + 2)) φ :=
  degenerateDiagram_boundary hcof hfib D n j φ value restriction i
example (i : Fin (n + 2)) : degeneracyFunctor D (n + 1) i ⋙
    filler hcof hfib D n j φ value restriction = degenerateDiagram hcof hfib D n φ value i :=
  filler_degeneracy hcof hfib D n j φ value compatible restriction i
end Extension

section Boundary
open CategoryTheory.MonoidalCategory OrdinaryBarChoiceBoundaryGluing
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {P : SSet.{max u v}} (n : ℕ)
  {X Y : OrdinaryBarChoiceCategory.Object (C := C) hcof hfib (parameters P (n + 1))}
  (a : Fin (n + 3) → (X ⟶ Y)) (h : Compatible hcof hfib n a)
example (k : Fin (n + 3)) :
    (OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι k)).map
      (boundaryHom hcof hfib n a h) = a k := boundaryHom_face hcof hfib n a h k
end Boundary

section FreeBoundary
open CategoryTheory.MonoidalCategory OrdinaryBarChoiceBoundaryGluing
open OrdinaryBarFreeDiagramExtension OrdinaryBarFreeBoundaryGluing
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {V : Type uV} [Quiver.{vV} V] {P : SSet.{max u v}} (n : ℕ)
  (φ : V ⥤q target (C := C) hcof hfib (parameters P (n + 1)))
  (a : Fin (n + 3) → {X Y : V} → (X ⟶ Y) → (φ.obj X ⟶ φ.obj Y))
  (h : ∀ {X Y : V} (e : X ⟶ Y), Compatible hcof hfib n (fun k => a k e))
example (k : Fin (n + 3)) : OrdinaryBarFreeBoundaryGluing.boundary hcof hfib n φ a h ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι k) =
      faceDiagram hcof hfib n φ a k :=
  OrdinaryBarFreeBoundaryGluing.boundary_face hcof hfib n φ a h k
end FreeBoundary

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeBoundaryGluing,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorLatchingValues,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeDegeneracyExtension,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryGluing]
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
    throwError "Missing free latching extension modules"
  logInfo m!"Free latching extension audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
