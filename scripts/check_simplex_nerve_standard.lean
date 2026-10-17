import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v u uH vH
noncomputable section
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.SimplicialModel

-- The new functor and natural augmentation are the original actual constructions.
example (X : SSet.{v}) : SimplexNerve.functor.obj X = nerve X.Elements := rfl
example (X : SSet.{v}) : SimplexNerve.augmentation.app X =
    SimplexNerveAugmentation.augmentation X := rfl

-- No model structure is an input to either structural property.
example : PreservesColimitsOfSize.{v, v} SimplexNerve.functor.{v} := inferInstance
example {X Y : SSet.{v}} (f : X ⟶ Y) [Mono f] :
    Mono (SimplexNerve.functor.map f) := inferInstance

example {J : Type v} [Category.{v} J] {F : J ⥤ SSet.{v}} (c : Cocone F)
    (hc : IsColimit c) : IsColimit (SimplexNerve.functor.mapCocone c) :=
  isColimitOfPreserves SimplexNerve.functor hc

-- Independent category object/Hom universes, with the actual terminal map as hom.
example {D : Type u} [Category.{v} D] {a : D} (ha : IsInitial a)
    {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    (NerveInitialImage.terminalImageIso ha L hL).hom =
      L.map (SSet.stdSimplex.isTerminalObj₀.from (nerve D)) := rfl

-- This also applies directly in an enlarged auxiliary universe, without a model there.
example {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) (n : ℕ) :
    IsIso (L.map (SimplexNerve.augmentation.app
      (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk n)))) :=
  SimplexNerve.standardAugmentation_isIso L hL n

example (n : ℕ) : IsIso (AnodyneHomotopy.anodyneQ.map
    (SimplexNerve.augmentation.app (SSet.stdSimplex.{v}.obj (SimplexCategory.mk n)))) :=
  SimplexNerve.standardAugmentation_isIso AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions) n

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNerveFunctor,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNerveMonos,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.NerveInitialContraction,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNerveStandard]
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
  unless modules.size == expected.size do throwError "Missing simplex-nerve modules"
  logInfo m!"Simplex nerve standard audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
