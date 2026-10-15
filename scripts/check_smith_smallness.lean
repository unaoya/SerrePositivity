import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w t v u
noncomputable section
open CategoryTheory CategoryTheory.Limits SerrePositivity.Smith

variable {C : Type u} [Category.{v} C]

-- The family index, objects and homs have independent universes.
example {ι : Type t} [Small.{w} ι] (a : ι → C) [∀ i, IsPresentable.{w} (a i)] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular), ∀ i, IsCardinalPresentable (a i) κ :=
  exists_common_presentability a

example [IsAccessibleCategory.{w} C] (I : MorphismProperty C) [I.IsSmall.{w}] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      ∀ i : I.toSet, IsCardinalPresentable i.val.left κ ∧
        IsCardinalPresentable i.val.right κ :=
  exists_common_arrow_presentability (fun i : I.toSet ↦ i.val)

-- No model structure and no SOA assumption are supplied by the consumer.
example [IsLocallyPresentable.{w} C] (I : MorphismProperty C) [I.IsSmall.{w}] :
    I.rlp.llp.HasFunctorialFactorization I.rlp := by
  have := hasSmallObjectArgument I
  infer_instance

-- The next Smith stage can apply the same theorem to R0's small target class.
example [IsLocallyPresentable.{w} C] (W I : MorphismProperty C) [I.IsSmall.{w}]
    [IsAccessibleCategory.{w} (Arrow C)]
    [IsAccessibleCategory.{w} (arrowProperty W).FullSubcategory]
    [(arrowInclusion W).IsAccessible.{w}] :
    (solutionTargetsForClass W I).HasSmallObjectArgument.{w} :=
  hasSmallObjectArgument (solutionTargetsForClass W I)

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.modules[idx.toNat]!.module ==
        `SerrePositivity.HomotopicalAlgebra.Smith.Smallness do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "No Smith smallness declarations audited"
  logInfo m!"Smith smallness audit passed: {count} declarations, standard axioms only."
