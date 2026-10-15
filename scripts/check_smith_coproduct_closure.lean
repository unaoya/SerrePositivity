import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits SerrePositivity.MorphismClosure

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
  (P : MorphismProperty C) [P.IsStableUnderCobaseChange]
  [P.IsStableUnderTransfiniteComposition.{w}]

-- No ordering, model structure, retract closure, or accessibility is supplied.
example {ι : Type w} {A B : ι → C} (f : ∀ i, A i ⟶ B i)
    (hf : ∀ i, P (f i)) : P (Limits.Sigma.map f) := sigma_mem P f hf

example : P.IsStableUnderCoproducts.{w} := stableUnderCoproducts P

-- The empty coproduct is included; it is not discarded by a Nonempty hypothesis.
example {A B : PEmpty.{w + 1} → C} (f : ∀ i, A i ⟶ B i) :
    P (Limits.Sigma.map f) := sigma_mem P f (fun i ↦ PEmpty.elim i)

example {C : Type u} [Category.{v} C] [IsLocallyPresentable.{w} C]
    (I J W : MorphismProperty C) [J.IsSmall.{w}] [W.IsStableUnderRetracts]
    [(I.rlp.llp ⊓ W).IsStableUnderCobaseChange]
    [(I.rlp.llp ⊓ W).IsStableUnderTransfiniteComposition.{w}]
    (hJ : J ≤ I.rlp.llp ⊓ W) : J.rlp.llp ≤ I.rlp.llp ⊓ W := by
  have := SerrePositivity.Smith.locallyPresentable_hasColimits (C := C)
  have := SerrePositivity.Smith.hasSmallObjectArgument J
  have := stableUnderCoproducts (I.rlp.llp ⊓ W)
  exact SerrePositivity.Smith.generatedLeft_le_of_closure I J W hJ

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.modules[idx.toNat]!.module ==
        `SerrePositivity.HomotopicalAlgebra.Smith.CoproductClosure do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "No coproduct closure declarations audited"
  logInfo m!"Coproduct closure audit passed: {count} declarations, standard axioms only."
