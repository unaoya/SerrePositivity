import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w v uD vD
noncomputable section
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.SimplicialModel

-- No ModelCategory is assumed in either value universe.
variable {D : Type uD} [Category.{vD} D] (L : SSet.{v} ⥤ D)
  [L.IsLocalization SSet.anodyneExtensions]
  (X K : SSet.{v}) (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

example (φ : L.obj X ⟶ L.obj K) :
    L.map (KanLocalizedRepresentatives.representative L hK φ) = φ :=
  KanLocalizedRepresentatives.representative_map L hK φ

example (f g : X ⟶ K) :
    L.map f = L.map g ↔ Nonempty (SSet.Homotopy f g) :=
  KanLocalizedRepresentatives.map_eq_iff_homotopy L hK f g

example : HomotopyClasses.obj X K ≃ (L.obj X ⟶ L.obj K) :=
  KanLocalizedRepresentatives.homEquiv L hK X

variable (M : SSet.{max w v} ⥤ D) [M.IsLocalization SSet.anodyneExtensions]

example : Small.{v} (M.obj (UniverseLift.obj.{w} X) ⟶
    M.obj (UniverseLift.obj.{w} K)) :=
  UniverseLift.small_localizedHom M X K hK

example (φ : M.obj (UniverseLift.obj.{w} X) ⟶ M.obj (UniverseLift.obj.{w} K)) :
    M.map (UniverseLift.map.{w} (UniverseLift.localizedRepresentative M X K hK φ)) = φ :=
  UniverseLift.localizedRepresentative_map M X K hK φ

example (f g : X ⟶ K) :
    M.map (UniverseLift.map.{w} f) = M.map (UniverseLift.map.{w} g) ↔
      Nonempty (SSet.Homotopy f g) :=
  UniverseLift.localized_map_eq_iff_homotopy M X K hK f g

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanLocalizedRepresentatives,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftLocalizedHom]
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
    throwError "Missing Kan localized representative modules"
  logInfo m!"Kan localized representative audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
