import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits SerrePositivity.Smith

variable {C : Type u} [Category.{v} C] [IsLocallyPresentable.{w} C]
  (I W : MorphismProperty C) [I.IsSmall.{w}] [W.HasTwoOutOfThreeProperty]
  [IsAccessibleCategory.{w} (Arrow C)]
  [IsAccessibleCategory.{w} (arrowProperty W).FullSubcategory]
  [(arrowInclusion W).IsAccessible.{w}] (hIW : I.rlp ≤ W)

-- Complete R2 consumer: no J, factorization or model structure is supplied.
example : ∃ J : MorphismProperty C, J.IsSmall.{w} ∧
    J.HasSmallObjectArgument.{w} ∧ J ≤ I.rlp.llp ⊓ W ∧
    ∀ (i f : Arrow C), I i.hom → W f.hom → ∀ sq : i ⟶ f,
      ∃ g : Arrow C, J g.hom ∧ ∃ (p : i ⟶ g) (q : g ⟶ f), p ≫ q = sq := by
  have := locallyPresentable_hasColimits (C := C)
  have := hasSmallObjectArgument I
  let J := generatingTrivialCofibrations I W hIW
  exact ⟨J, inferInstance, hasSmallObjectArgument J,
    generatingTrivialCofibrations_le I W hIW,
    fun i f hi hf sq ↦ generatingTrivialCofibrations_factor I W hIW i f hi hf sq⟩

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.modules[idx.toNat]!.module ==
        `SerrePositivity.HomotopicalAlgebra.Smith.GeneratingTrivialCofibrations do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "No Smith generating declarations audited"
  logInfo m!"Smith generating audit passed: {count} declarations, standard axioms only."
