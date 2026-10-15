import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w v u
open CategoryTheory CategoryTheory.Limits SerrePositivity.Smith

-- Object and hom universes need not equal the local presentability universe.
example {C : Type u} [Category.{v} C] [IsLocallyPresentable.{w} C] :
    HasLimitsOfSize.{w, w} C := locallyPresentable_hasLimits

example {C : Type u} [Category.{v} C] [IsLocallyPresentable.{w} C] :
    HasFiniteLimits C := by
  have := locallyPresentable_hasLimits (C := C)
  exact hasFiniteLimits_of_hasLimitsOfSize C

-- The small dense embedding lemma itself requires no presentability assumption.
example {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]
    {D : Type w} [SmallCategory D] (F : D ⥤ C) [F.IsDense] :
    HasLimitsOfSize.{w, w} C := hasLimits_of_small_dense F

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.modules[idx.toNat]!.module ==
        `SerrePositivity.HomotopicalAlgebra.Smith.Completeness do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "No Smith completeness declarations audited"
  logInfo m!"Smith completeness audit passed: {count} declarations, standard axioms only."
