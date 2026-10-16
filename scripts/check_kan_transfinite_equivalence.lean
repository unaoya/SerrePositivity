import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w u v
noncomputable section
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.SimplicialModel
open KanTestLiftingClass

-- The value universe is independent and may be enlarged, with no model there.
example : localizedMonos.{max u v} =
    MorphismProperty.monomorphisms SSet.{max u v} ⊓ rightTests.llp := localizedMonos_eq

-- The converse lifting criterion detects the original localization even for nonmonos.
example {A B : SSet.{max u v}} (i : A ⟶ B) (hi : rightTests.llp i) :
    IsIso (AnodyneHomotopy.anodyneQ.map i) := localized_isIso_of_llp i hi

-- The shape universe is independent; only its actual size is required to fit.
example (J : Type w) [Small.{max u v} J] [LinearOrder J] [SuccOrder J] [OrderBot J]
    [WellFoundedLT J] (F : J ⥤ SSet.{max u v}) [F.IsWellOrderContinuous]
    (hF : ∀ j, ¬IsMax j → localizedMonos (F.map (homOfLE (Order.le_succ j))))
    (c : Cocone F) (hc : IsColimit c) :
    Mono (c.ι.app ⊥) ∧ IsIso (AnodyneHomotopy.anodyneQ.map (c.ι.app ⊥)) :=
  KanLocalizedTransfinite.cocone_mem J F hF c hc

-- A genuine countable colimit; neither a terminal stage nor preservation by Q is assumed.
example (F : ℕ ⥤ SSet.{max u v})
    (hF : ∀ n, Mono (F.map (homOfLE (Nat.le_succ n))) ∧
      IsIso (AnodyneHomotopy.anodyneQ.map (F.map (homOfLE (Nat.le_succ n)))))
    (c : Cocone F) (hc : IsColimit c) :
    IsIso (AnodyneHomotopy.anodyneQ.map (c.ι.app 0)) :=
  (KanLocalizedTransfinite.sequential_cocone_mem F hF c hc).2

example : MorphismProperty.IsStableUnderTransfiniteComposition.{max u v}
    localizedMonos.{max u v} := inferInstance

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanRelativeLifting,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanTestLiftingClass,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanLocalizedTransfinite]
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
  unless modules.size == expected.size do throwError "Missing Kan transfinite equivalence modules"
  logInfo m!"Kan transfinite equivalence audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
