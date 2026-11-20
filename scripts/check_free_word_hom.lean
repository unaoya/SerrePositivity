import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFixedRowWordHom
import Lean.Util.CollectAxioms

universe u v w w' uH vH
noncomputable section
open CategoryTheory
open SerrePositivity SerrePositivity.SimplicialModel

section NormalForm
open QuiverWeightedPaths
variable (V : Type u) [Quiver.{v} V] (M : Type w) [Monoid M] (X Y : V)
example : Path V M X Y ≃ ((targetSource V M).obj X ⟶ (targetSource V M).obj Y) :=
  normalFormEquiv V M X Y
example (p : Path V M X Y) : (decode V M).map (eval V M p) = p := decode_eval V M p
example (f : (targetSource V M).obj X ⟶ (targetSource V M).obj Y) :
    eval V M ((decode V M).map f) = f := (normalFormEquiv V M X Y).apply_symm_apply f
example (p : Path V M X Y) : (AmbientWords.augmentation (Paths V) M).map (eval V M p) =
    forget p := augmentation_eval V M p
end NormalForm

section Parameter
open QuiverWeightedPaths
variable (V : Type u) [Quiver.{v} V] {M : Type w} [MonoidWithZero M]
  {N : Type w'} [MonoidWithZero N] (h : M →*₀ N) {X Y : V}
example (p : Path V M X Y) : (AmbientWords.map (𝟭 (Paths V)) h).map (eval V M p) =
    eval V N (mapWeights h p) := map_eval V h p
end Parameter

section Simplicial
variable (V : Type u) [Quiver.{v} V] (X Y : V)
example : SSet.Homotopy (𝟙 (WeightedWordHom.hom V X Y))
    (WeightedWordHom.projection V X Y ≫ WeightedWordHom.section_ V X Y) :=
  WeightedWordHom.contraction V X Y
example {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    L.obj (WeightedWordHom.hom V X Y) ≅ L.obj (WeightedWordHom.base V X Y) :=
  WeightedWordHom.comparisonIso V X Y L hL
example : FreeWordHom.hom V X Y ≅ WeightedWordHom.hom V X Y := FreeWordHom.comparisonIso V X Y
example : IsIso (AnodyneHomotopy.anodyneQ.map (FreeWordHom.augmentation V X Y)) :=
  FreeWordHom.localized_augmentation_isIso V X Y
example (n : SimplexCategoryᵒᵖ) (f : (FreeWordHom.hom V X Y).obj n) :
    (FreeWordHom.augmentation V X Y).app n f = ULift.up
      ((AmbientWords.augmentation (Paths V) (WordSegment.degree.{max u v} n)).map f) :=
  FreeWordHom.augmentation_app V X Y n f
end Simplicial

open HomotopyFunctionComplex OrdinaryBarFreeResolutionSeed
-- The actual outer source degrees, with no model category or large SSet model assumed.
example (C : Type u) [Category.{v} C] (N : ℕ) (X Y : D C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (OrdinaryBarFixedRowWordHom.augmentation C N X Y)) :=
  OrdinaryBarFixedRowWordHom.localized_augmentation_isIso C N X Y

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.WeightedWordHom,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.FreeWordHom,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFixedRowWordHom]
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
  unless modules.size == expected.size do throwError "Missing free word Hom modules"
  logInfo m!"Free word Hom audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
