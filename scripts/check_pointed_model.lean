import SerrePositivity.HomotopicalAlgebra.Foundations
import SerrePositivity.Spectra.General.Foundations
import SerrePositivity.Spectra.StageTwo
import Lean.Util.CollectAxioms

universe v u
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity SerrePositivity.PointedObject SerrePositivity.PointedModel
open SerrePositivity.Quillen
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [ModelCategory C]

example {X Y : PointedObject C} (f : X ⟶ Y) :
    Cofibration f ↔ Cofibration f.right := cofibration_iff_underlying f

example {X Y : PointedObject C} (f : X ⟶ Y) :
    Fibration f ↔ Fibration f.right := fibration_iff_underlying f

example {X Y : PointedObject C} (f : X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence f.right := weakEquivalence_iff_underlying f

example (X : PointedObject C) : IsCofibrant X ↔ Cofibration X.hom :=
  isCofibrant_iff_basepoint X

example : IsRightQuillen (forget (C := C)) := forget_isRightQuillen
example : IsLeftQuillen (adjoinFunctor (C := C)) := adjoin_isLeftQuillen
example (X : C) [IsCofibrant X] : IsCofibrant (adjoin X) := adjoin_isCofibrant X
example [IsCofibrant (𝟙_ C)] : IsCofibrant (sphereZero (C := C)) := sphereZero_isCofibrant

-- These are the existing smash unit and its unit axiom, without assuming smash SM7.
example [MonoidalClosed C] [IsCofibrant (𝟙_ C)] : IsCofibrant (𝟙_ (PointedObject C)) :=
  smashUnit_isCofibrant
example [MonoidalClosed C] [IsCofibrant (𝟙_ C)] : HasUnitAxiom (PointedObject C) :=
  smash_hasUnitAxiom

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.modules[idx.toNat]!.module ==
        `SerrePositivity.HomotopicalAlgebra.Pointed.Basic do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "No pointed model declarations audited"
  logInfo m!"Pointed model audit passed: {count} declarations, standard axioms only."
