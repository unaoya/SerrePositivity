import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SerrePositivity.SimplicialModel

-- All values can lie in the auxiliary universe; no model there is assumed.
variable {A B C P K : SSet.{max u v}} (i : A ⟶ B) [Mono i]
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

-- The originally selected endpoint and the entire restricted homotopy are retained.
example (b : B ⟶ K) (a : A ⟶ K) (H : SSet.Homotopy (i ≫ b) a) :
    ∃ g : B ⟶ K, i ≫ g = a ∧ ∃ H' : SSet.Homotopy b g,
      i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ H'.h = H.h :=
  KanMonoEndpointExtension.exists_from_zero i hK b a H

example (b : B ⟶ K) (a : A ⟶ K) (H : SSet.Homotopy a (i ≫ b)) :
    ∃ g : B ⟶ K, i ≫ g = a ∧ ∃ H' : SSet.Homotopy g b,
      i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ H'.h = H.h :=
  KanMonoEndpointExtension.exists_from_one i hK b a H

-- Equality in the quotient can be a whole generated zigzag, not one selected interval.
example {a a' : A ⟶ K} (h : HomotopyClasses.mk a = HomotopyClasses.mk a')
    (ha : KanMonoStrictExtension.Extends i a) : KanMonoStrictExtension.Extends i a' :=
  KanMonoStrictExtension.extends_of_class_eq i hK h ha

-- Surjectivity alone suffices for strict extension of the original prescribed map.
example (hs : Function.Surjective (HomotopyClasses.pre i (K := K))) (a : A ⟶ K) :
    ∃ b : B ⟶ K, i ≫ b = a :=
  KanMonoStrictExtension.exists_extension_of_surjective i hK hs a

example (hi : IsIso (AnodyneHomotopy.anodyneQ.map i)) :
    HasLiftingProperty i (terminal.from K) :=
  KanMonoStrictExtension.terminal_lifting i hK hi

-- An arbitrary actual pushout, including a non-mono other leg, preserves strict extension.
example (j : A ⟶ C) (u : B ⟶ P) (g : C ⟶ P) (sq : IsPushout i j u g)
    (hi : IsIso (AnodyneHomotopy.anodyneQ.map i)) (a : C ⟶ K) :
    ∃ b : P ⟶ K, g ≫ b = a :=
  KanMonoPushoutExtension.exists_extension i j u g sq hi hK a

-- This is the surjective half only; no injectivity or localized isomorphism is inferred.
example (j : A ⟶ C) (u : B ⟶ P) (g : C ⟶ P) (sq : IsPushout i j u g)
    (hi : IsIso (AnodyneHomotopy.anodyneQ.map i)) :
    Function.Surjective (HomotopyClasses.pre g (K := K)) :=
  KanMonoPushoutExtension.pre_surjective i j u g sq hi hK

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoEndpointExtension,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoStrictExtension,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoPushoutExtension]
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
  unless modules.size == expected.size do throwError "Missing Kan mono extension modules"
  logInfo m!"Kan mono extension audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
