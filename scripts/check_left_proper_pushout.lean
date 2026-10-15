import SerrePositivity.HomotopicalAlgebra.Quillen.LeftProper
import Lean.Util.CollectAxioms

noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

-- No properness or cofibrancy condition on the base object or base map.
example {X Y : C} (f : X ⟶ Y) :
    SerrePositivity.Quillen.IsLeftQuillen (Under.pushout f) := inferInstance

example {X Y : C} (f : X ⟶ Y) {A B : Under X} (a : A ⟶ B)
    (hA : cofibrations C A.hom) (hB : cofibrations C B.hom)
    (ha : weakEquivalences C a.right) :
    weakEquivalences C ((Under.pushout f).map a).right :=
  SerrePositivity.UnderModel.pushout_map_weakEquivalence f a hA hB ha

-- Left properness is stated for the original classes using Mathlib's relative stability contract.
example [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]
    {A B D A' B' D' : C} (f : A ⟶ B) (g : A ⟶ D) (f' : A' ⟶ B') (g' : A' ⟶ D')
    (a : A ⟶ A') (b : B ⟶ B') (c : D ⟶ D')
    (hf : cofibrations C f) (hf' : cofibrations C f')
    (ha : weakEquivalences C a) (hb : weakEquivalences C b) (hc : weakEquivalences C c)
    (ef : f ≫ b = a ≫ f') (eg : g ≫ c = a ≫ g') :
    weakEquivalences C (pushout.map f g f' g' b c a ef eg) :=
  SerrePositivity.Quillen.pushout_map_weakEquivalence f g f' g' a b c hf hf' ha hb hc ef eg

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Under.Quillen,
    `SerrePositivity.HomotopicalAlgebra.Quillen.LeftProper]
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
  logInfo m!"Under/left proper pushout audit passed: {count} declarations in {seen.size} modules."
