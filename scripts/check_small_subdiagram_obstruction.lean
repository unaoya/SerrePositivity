import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open SerrePositivity.SimplicialModel
open SmallSubdiagramObstruction

-- All tests are model-free, including the auxiliary large value universe.
example {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) : X.Nonempty ↔ Y.Nonempty :=
  AnodyneNonempty.nonempty_iff_of_localized_isIso f hf

example {I : Type u} {A B : SSet.{u}} (j : A ⟶ B) [Mono j]
    (f : A ⟶ nerve (Codiscrete I)) (i : I) :
    ∃ g : B ⟶ nerve (Codiscrete I), j ≫ g = f :=
  CodiscreteNerveExtension.exists_extension j f i

-- The indexing category is large but even locally small in universe zero.
example (I : Type u) : LocallySmall.{0} (Index I) := inferInstance

example (I : Type u) (i : I) (d : Index I) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from ((diagram I).obj d)) :=
  values_kan I i d

example (I : Type u) (i : I) {d e : Index I} (f : d ⟶ e) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((diagram I).map f)) := map_isIso i f

-- No natural comparison from any small-valued diagram can be equivalent at all leaves.
example (G : Index (Type v) ⥤ SSet.{v})
    (α : G ⋙ SSet.uliftFunctor.{v + 1, v} ⟶ diagram (Type v))
    (hα : ∀ i, IsIso (AnodyneHomotopy.anodyneQ.map (α.app (leaf (Type v) i)))) : False :=
  no_small_diagram_comparison G α hα

-- In the reverse direction the actual natural small quotient is inverted componentwise.
example : IsIso (Functor.whiskerRight smallQuotient.{v} AnodyneHomotopy.anodyneQ) :=
  smallQuotient_isIso

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneNonempty,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.CodiscreteNerveExtension,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.SmallSubdiagramObstruction]
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
    throwError "Missing small subdiagram obstruction modules"
  logInfo m!"Small subdiagram obstruction audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
