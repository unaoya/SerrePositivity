import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarSourceContraction
import Lean.Util.CollectAxioms

universe u v uH vH
noncomputable section
open CategoryTheory
open SerrePositivity SerrePositivity.SimplicialModel

-- Actual standard-interval contraction, in any value universe, without a model structure.
example {A : SimplicialObject.Augmented (Type v)}
    (ed : SimplicialObject.Augmented.ExtraDegeneracy A) :
    SSet.Homotopy (A.hom ≫ ed.section_) (𝟙 A.left) :=
  ExtraDegeneracyContraction.contraction ed
example {A : SimplicialObject.Augmented (Type v)}
    (ed : SimplicialObject.Augmented.ExtraDegeneracy A)
    {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    L.obj A.left ≅ L.obj ((SimplicialObject.const (Type v)).obj A.right) :=
  ExtraDegeneracyContraction.comparisonIso ed L hL
example {X Y : SSet.{v}} {f g : X ⟶ Y} (h : SSet.Homotopy f g) :
    SSet.Homotopy (OppositeHomotopy.reverseMap g) (OppositeHomotopy.reverseMap f) :=
  OppositeHomotopy.homotopy h

-- Only a category is needed; object and Hom universes remain independent.
open HomotopyFunctionComplex OrdinaryBarFreeResolutionSeed
variable (C : Type u) [Category.{v} C] (X Y : D C)
example : SimplicialObject.Augmented.ExtraDegeneracy
    (OrdinaryBarSourceExtraDegeneracy.augmented C X Y) :=
  OrdinaryBarSourceExtraDegeneracy.extraDegeneracy C X Y
example : IsIso (AnodyneHomotopy.anodyneQ.map (OrdinaryBarSourceHom.augmentation C X Y)) :=
  OrdinaryBarSourceContraction.source_augmentation_isIso C X Y
example : IsIso (AnodyneHomotopy.anodyneQ.map
    (OrdinaryBarAmbientWordComparison.augmentation C X Y)) :=
  OrdinaryBarSourceContraction.word_augmentation_isIso C X Y
example : IsIso (AnodyneHomotopy.anodyneQ.map
    (OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X Y)) :=
  OrdinaryBarSourceContraction.small_augmentation_isIso C X Y

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.CategoryTheory.Simplex.Prefix,
    `SerrePositivity.CategoryTheory.Simplex.PrefixInterval,
    `SerrePositivity.CategoryTheory.Quiver.PathObjectTransport,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.ExtraDegeneracyInterval,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.ExtraDegeneracyContraction,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.OppositeHomotopy,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarSourceOperators,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarSourceExtraOperators,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarSourceExtraDegeneracy,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarSourceContraction]
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
  unless modules.size == expected.size do throwError "Missing source contraction modules"
  logInfo m!"Source contraction audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
