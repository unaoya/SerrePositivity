import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.CompatibleHornFillingOperation
import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.DegenerateHornInput
import Lean.Util.CollectAxioms

universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel

section Union
variable {J : Type u} {B E : SSet.{v}} (S : J → SSet.{v})
  (b : ∀ j, S j ⟶ B) (a : ∀ j, S j ⟶ E)
  (h : CompatibleInputUnion.Compatible S b a) (p : E ⟶ B) (hp : ∀ j, a j ≫ p = b j)

-- No Small J, Mono (b j), or universe equality is assumed.
example : SSet.{v} := (CompatibleInputUnion.inputs S b).toSSet
example : CompatibleInputUnion.lift S b a h ≫ p = (CompatibleInputUnion.inputs S b).ι :=
  CompatibleInputUnion.lift_over S b a h p hp
example (j : J) : CompatibleInputUnion.toInputs S b j ≫ CompatibleInputUnion.lift S b a h =
    a j := CompatibleInputUnion.toInputs_lift S b a h j
end Union

section ManyPrescriptions
variable (K : SSet.{v}) {n : ℕ} (i : Fin (n + 2))
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))
  {J : Type u} (S : J → SSet.{v})
  (b : ∀ j, S j ⟶ (ihom (SSet.horn (n + 1) i).toSSet).obj K)
  (a : ∀ j, S j ⟶ (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).obj K)
  (h : CompatibleInputUnion.Compatible S b a)
  (ha : ∀ j, a j ≫ KanHornFamilyLifting.restriction K i = b j)
example : CompatibleHornFillingOperation.section_ K i hK S b a h ha ≫
    KanHornFamilyLifting.restriction K i = 𝟙 _ :=
  CompatibleHornFillingOperation.section_restriction K i hK S b a h ha
example (j : J) {L : SSet.{v}} (q : L ⟶ S j) :
    uncurry (CompatibleHornFillingOperation.fill K i hK S b a h ha (q ≫ b j)) =
      SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ◁ q ≫ uncurry (a j) :=
  CompatibleHornFillingOperation.family_prescribed K i hK S b a h ha j q
end ManyPrescriptions

-- Arbitrarily many repeated degenerate input families really satisfy overlap compatibility.
example {J : Type u} (K : SSet.{v}) {n : ℕ} (i : Fin (n + 2)) (d : Fin (n + 1)) :
    CompatibleInputUnion.Compatible
      (fun _ : J => (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).obj K)
      (fun _ => DegenerateHornInput.boundary i d K)
      (fun _ => DegenerateHornInput.degeneracy d K) := by
  intro j k m x y h
  have hx : x = y :=
    ((CategoryTheory.mono_iff_injective ((DegenerateHornInput.boundary i d K).app m)).mp
      inferInstance) h
  exact congrArg ((DegenerateHornInput.degeneracy d K).app m) hx

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.CompatibleInputUnion,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.CompatibleHornFillingOperation]
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
  unless modules.size == expected.size do throwError "Missing compatible input modules"
  logInfo m!"Compatible input audit passed: {count} declarations in {modules.size} modules."
