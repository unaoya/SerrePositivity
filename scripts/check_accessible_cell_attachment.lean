import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w u
noncomputable section
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.Smith SerrePositivity.Smith.AccessibleCellAttachment

variable {C : Type u} [Category.{w} C] {ι : Type w}

-- Accessibility is derived for Mathlib's actual successor, not postulated.
example [HasColimitsOfSize.{w, w} C] (a : ι → Arrow C)
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [∀ i, IsCardinalPresentable (a i).left κ]
    [∀ i, IsCardinalPresentable (a i).right κ] :
    (SmallObject.functor (fun i ↦ (a i).hom)).IsCardinalAccessible κ :=
  step_isCardinalAccessible a κ

example [IsLocallyPresentable.{w} C] (a : ι → Arrow C) :
    letI := locallyPresentable_hasColimits (C := C)
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      (SmallObject.functor (fun i ↦ (a i).hom)).IsCardinalAccessible κ := by
  have := locallyPresentable_hasColimits (C := C)
  obtain ⟨κ, hκ, ha⟩ := exists_common_arrow_presentability a
  have : ∀ i, IsCardinalPresentable (a i).left κ := fun i ↦ (ha i).1
  have : ∀ i, IsCardinalPresentable (a i).right κ := fun i ↦ (ha i).2
  exact ⟨κ, hκ, step_isCardinalAccessible a κ⟩

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.modules[idx.toNat]!.module ==
        `SerrePositivity.HomotopicalAlgebra.Smith.AccessibleCellAttachment do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "Cell attachment module was not audited"
  logInfo m!"Accessible cell attachment audit passed: {count} declarations, standard axioms only."
