import SerrePositivity.HomotopicalAlgebra.Quillen.Saturation
import Lean.Util.CollectAxioms

noncomputable section
universe v u vH uH
open CategoryTheory HomotopicalAlgebra SerrePositivity.Quillen

-- General source model, arbitrary localization and independent universes.
-- No functorial-factorization, accessibility or combinatoriality input.
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {H : Type uH} [Category.{vH} H] (L : C ⥤ H)
  [L.IsLocalization (weakEquivalences C)]

example {X Y : C} (f : X ⟶ Y) : weakEquivalences C f ↔ IsIso (L.map f) :=
  weakEquivalences_iff_isIso_map L f

example : weakEquivalences C = (MorphismProperty.isomorphisms H).inverseImage L :=
  weakEquivalences_eq_inverseImage_isomorphisms L

-- The canonical formal localization supplies an unconditional application.
example {X Y : C} (f : X ⟶ Y)
    (hf : IsIso ((weakEquivalences C).Q.map f)) : weakEquivalences C f :=
  (weakEquivalences_iff_isIso_map (weakEquivalences C).Q f).mpr hf

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Quillen.WhiteheadConverse,
    `SerrePositivity.HomotopicalAlgebra.Quillen.Saturation]
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
  logInfo m!"Model saturation audit passed: {count} declarations in {seen.size} modules."
